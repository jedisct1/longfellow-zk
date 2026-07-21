//! Layered arithmetic circuits in quad representation, and their
//! serialization format.
//!
//! Layer j computes wires V[j] from V[j+1] as
//!
//!     V[j][g] = SUM_{l,r} Q[j][g, l, r] * V[j+1][l] * V[j+1][r]
//!
//! where the sparse Q is stored as a list of quads (g, h0, h1, v).
//! A quad whose constant is zero is an in-circuit assertion (a Z quad):
//! the corresponding combination of input wires must evaluate to zero.
//! Layer 0 produces the circuit outputs, which must all be zero for the
//! checked statement to hold.
//!
//! The byte format matches the reference implementation: all sizes are
//! 3-byte little-endian, quad indices are delta-encoded against the
//! previous quad with the least significant bit as sign, and the stream
//! ends with a 32-byte structural SHA-256 identifier.
//! SPEC_ISSUES.md lists where this diverges from the draft.

const std = @import("std");
const Allocator = std.mem.Allocator;
const Sha256 = std.crypto.hash.sha2.Sha256;
const assert = std.debug.assert;

const field = @import("field.zig");
pub const FieldId = field.FieldId;

pub const size_len = 3;
pub const id_len = 32;
pub const max_size = (1 << (8 * size_len)) - 1;
pub const max_layers = 10000;

pub const fieldIdOf = field.fieldIdOf;

pub const DeserializeError = error{
    Malformed,
    UnsupportedVersion,
    WrongField,
    IdMismatch,
} || Allocator.Error;

pub const EvaluateError = error{
    WrongInputCount,
    UnsupportedCopies,
    AssertionFailed,
} || Allocator.Error;

pub fn Circuit(comptime F: type) type {
    return struct {
        /// Number of output wires (per copy).
        nv: usize,
        /// Number of copies of the circuit.
        /// Only 1 is supported by evaluation and sumcheck for now.
        nc: usize,
        /// Number of public inputs; also the index of the first private
        /// input.
        npub_in: usize,
        /// Least input wire index not known to lie in the subfield.
        subfield_boundary: usize,
        /// Total number of input wires, public and private.
        ninputs: usize,
        /// Constants referenced by the quads.
        constants: []F,
        /// Layers in evaluation order: layers[0] produces the outputs and
        /// layers[layers.len - 1] consumes the inputs.
        layers: []Layer,
        /// Structural identifier; see `computeId`.
        id: [id_len]u8,

        const Self = @This();

        pub const Layer = struct {
            /// Number of sumcheck binding rounds for a wire index, i.e.
            /// ceil(log2(nw)).
            logw: usize,
            /// Number of input wires of this layer.
            nw: usize,
            quads: []Quad,
        };

        pub const Quad = struct {
            g: usize,
            h0: usize,
            h1: usize,
            /// Index into `constants`.
            /// A zero constant marks a Z quad.
            v: usize,
        };

        pub fn deinit(c: *Self, gpa: Allocator) void {
            for (c.layers) |layer| gpa.free(layer.quads);
            gpa.free(c.layers);
            gpa.free(c.constants);
            c.* = undefined;
        }

        pub fn logNumOutputs(c: Self) usize {
            return std.math.log2_int_ceil(usize, c.nv);
        }

        /// Total number of quads across all layers.
        pub fn numTerms(c: Self) usize {
            var n: usize = 0;
            for (c.layers) |layer| n += layer.quads.len;
            return n;
        }

        /// Parses the reference byte format.
        /// With `enforce_id`, the trailing identifier must match the
        /// recomputed one.
        pub fn fromBytes(gpa: Allocator, bytes: []const u8, enforce_id: bool) DeserializeError!Self {
            var r: ByteReader = .{ .bytes = bytes };

            if (try r.byte() != 0x01) return error.UnsupportedVersion;
            if (try r.size() != @backingInt(fieldIdOf(F))) return error.WrongField;
            const nv = try r.size();
            const nc = try r.size();
            const npub_in = try r.size();
            const subfield_boundary = try r.size();
            const ninputs = try r.size();
            const nl = try r.size();
            const numconst = try r.size();
            if (nv == 0 or nc == 0 or nl == 0 or nl > max_layers or
                npub_in > ninputs or subfield_boundary > ninputs)
            {
                return error.Malformed;
            }

            var c: Self = .{
                .nv = nv,
                .nc = nc,
                .npub_in = npub_in,
                .subfield_boundary = subfield_boundary,
                .ninputs = ninputs,
                .constants = &.{},
                .layers = &.{},
                .id = undefined,
            };
            errdefer c.deinit(gpa);

            // Check the declared sizes against the remaining input before
            // allocating, so a short but boastful header cannot force
            // large allocations.
            if (r.remaining() / F.encoded_len < numconst) return error.Malformed;
            c.constants = try gpa.alloc(F, numconst);
            for (c.constants) |*e| {
                e.* = F.fromBytes(try r.elt(F.encoded_len)) catch return error.Malformed;
            }

            c.layers = try gpa.alloc(Layer, nl);
            // On error, deinit must only free the quads slices that exist.
            for (c.layers) |*l| l.quads = &.{};

            var max_g = nv;
            for (c.layers) |*layer| {
                const logw = try r.size();
                const nw = try r.size();
                const nq = try r.size();
                if (nw == 0 or nw > std.math.shl(usize, 1, logw) or logw > size_len * 8) {
                    return error.Malformed;
                }
                layer.logw = logw;
                layer.nw = nw;
                if (r.remaining() / (4 * size_len) < nq) return error.Malformed;
                layer.quads = try gpa.alloc(Quad, nq);

                var prev: Quad = .{ .g = 0, .h0 = 0, .h1 = 0, .v = 0 };
                for (layer.quads) |*q| {
                    const g = try r.delta(prev.g);
                    const h0 = try r.delta(prev.h0);
                    const h1 = try r.delta(prev.h1);
                    const v = try r.size();
                    if (g >= max_g or h0 >= nw or h1 >= nw or v >= numconst) {
                        return error.Malformed;
                    }
                    q.* = .{ .g = g, .h0 = h0, .h1 = h1, .v = v };
                    prev = q.*;
                }
                max_g = nw;
            }

            const stored_id = bytes[r.pos..];
            if (stored_id.len != id_len) return error.Malformed;
            @memcpy(&c.id, stored_id);
            if (enforce_id and !std.mem.eql(u8, &c.id, &c.computeId())) {
                return error.IdMismatch;
            }
            return c;
        }

        /// Byte length of the serialized circuit.
        pub fn serializedSize(c: Self) usize {
            var n: usize = 1 + 8 * size_len + c.constants.len * F.encoded_len + id_len;
            for (c.layers) |layer| n += (3 + 4 * layer.quads.len) * size_len;
            return n;
        }

        /// Serializes to the reference byte format, using the stored id.
        /// `out` must hold at least serializedSize(c) bytes; the used
        /// prefix is returned.
        pub fn toBytes(c: Self, out: []u8) []u8 {
            var w: ByteWriter = .{ .out = out };

            w.byte(0x01);
            w.size(@backingInt(fieldIdOf(F)));
            w.size(c.nv);
            w.size(c.nc);
            w.size(c.npub_in);
            w.size(c.subfield_boundary);
            w.size(c.ninputs);
            w.size(c.layers.len);
            w.size(c.constants.len);
            for (c.constants) |e| w.bytes(&e.toBytes());

            for (c.layers) |layer| {
                w.size(layer.logw);
                w.size(layer.nw);
                w.size(layer.quads.len);
                var prev: Quad = .{ .g = 0, .h0 = 0, .h1 = 0, .v = 0 };
                for (layer.quads) |q| {
                    w.delta(q.g, prev.g);
                    w.delta(q.h0, prev.h0);
                    w.delta(q.h1, prev.h1);
                    w.size(q.v);
                    prev = q;
                }
            }

            w.bytes(&c.id);
            return out[0..w.pos];
        }

        /// The structural identifier: a SHA-256 over the field description
        /// and every size and quad of the circuit, in a fixed encoding
        /// shared with the reference implementation.
        pub fn computeId(c: Self) [id_len]u8 {
            var h = Sha256.init(.{});
            if (comptime @hasDecl(F, "modulus")) {
                update8(&h, 0x1);
                update8Elt(&h, F.zero.sub(F.one));
            } else {
                update8(&h, 0x2);
                update8(&h, F.bits);
            }
            update8(&h, c.nv);
            update8(&h, c.logNumOutputs());
            update8(&h, c.nc);
            update8(&h, std.math.log2_int_ceil(usize, c.nc));
            update8(&h, c.layers.len);
            update8(&h, c.ninputs);
            update8(&h, c.npub_in);
            update8(&h, c.subfield_boundary);
            for (c.layers) |layer| {
                update8(&h, layer.nw);
                update8(&h, layer.logw);
                update8(&h, layer.quads.len);
                for (layer.quads) |q| {
                    update8(&h, q.g);
                    update8(&h, q.h0);
                    update8(&h, q.h1);
                    update8Elt(&h, c.constants[q.v]);
                }
            }
            var out: [id_len]u8 = undefined;
            h.final(&out);
            return out;
        }

        /// Evaluates the circuit and returns all wire levels: result[j]
        /// are the wires computed by layer j, and result[layers.len] holds
        /// the inputs padded to the width of the last layer.
        /// Z quads must sum to zero.
        /// The caller owns the returned slices.
        pub fn evaluate(c: Self, gpa: Allocator, inputs: []const F) EvaluateError![][]F {
            if (c.nc != 1) return error.UnsupportedCopies;
            if (inputs.len != c.ninputs) return error.WrongInputCount;

            const nl = c.layers.len;
            const wires = try gpa.alloc([]F, nl + 1);
            for (wires) |*w| w.* = &.{};
            errdefer freeWires(gpa, wires);

            wires[nl] = try gpa.alloc(F, @max(c.ninputs, c.layers[nl - 1].nw));
            @memcpy(wires[nl][0..inputs.len], inputs);
            @memset(wires[nl][inputs.len..], F.zero);

            var j = nl;
            while (j > 0) {
                j -= 1;
                const in = wires[j + 1];
                const width = if (j == 0) c.nv else c.layers[j - 1].nw;
                const out = try gpa.alloc(F, width);
                @memset(out, F.zero);
                wires[j] = out;

                for (c.layers[j].quads) |q| {
                    const k = c.constants[q.v];
                    const prod = in[q.h0].mul(in[q.h1]);
                    out[q.g] = out[q.g].add(if (k.isZero()) prod else k.mul(prod));
                }
                for (c.layers[j].quads) |q| {
                    if (c.constants[q.v].isZero() and !out[q.g].isZero()) {
                        return error.AssertionFailed;
                    }
                }
            }
            return wires;
        }

        pub fn freeWires(gpa: Allocator, wires: [][]F) void {
            for (wires) |w| gpa.free(w);
            gpa.free(wires);
        }

        fn update8Elt(h: *Sha256, e: F) void {
            h.update(&e.toBytes());
        }
    };
}

fn update8(h: *Sha256, x: u64) void {
    var b: [8]u8 = undefined;
    std.mem.writeInt(u64, &b, x, .little);
    h.update(&b);
}

const ByteReader = struct {
    bytes: []const u8,
    pos: usize = 0,

    fn remaining(r: ByteReader) usize {
        return r.bytes.len - r.pos;
    }

    fn byte(r: *ByteReader) error{Malformed}!u8 {
        if (r.pos >= r.bytes.len) return error.Malformed;
        defer r.pos += 1;
        return r.bytes[r.pos];
    }

    fn size(r: *ByteReader) error{Malformed}!usize {
        if (r.remaining() < size_len) return error.Malformed;
        defer r.pos += size_len;
        return std.mem.readVarInt(usize, r.bytes[r.pos..][0..size_len], .little);
    }

    fn delta(r: *ByteReader, prev: usize) error{Malformed}!usize {
        const d = try r.size();
        const mag = d >> 1;
        if (d & 1 != 0) {
            if (mag > prev) return error.Malformed;
            return prev - mag;
        }
        return prev + mag;
    }

    fn elt(r: *ByteReader, comptime n: usize) error{Malformed}![n]u8 {
        if (r.remaining() < n) return error.Malformed;
        defer r.pos += n;
        return r.bytes[r.pos..][0..n].*;
    }
};

const ByteWriter = struct {
    out: []u8,
    pos: usize = 0,

    fn byte(w: *ByteWriter, b: u8) void {
        w.out[w.pos] = b;
        w.pos += 1;
    }

    fn bytes(w: *ByteWriter, b: []const u8) void {
        @memcpy(w.out[w.pos..][0..b.len], b);
        w.pos += b.len;
    }

    fn size(w: *ByteWriter, v: usize) void {
        assert(v <= max_size);
        std.mem.writeInt(u24, w.out[w.pos..][0..size_len], @intCast(v), .little);
        w.pos += size_len;
    }

    fn delta(w: *ByteWriter, cur: usize, prev: usize) void {
        const d = if (cur >= prev) 2 * (cur - prev) else 2 * (prev - cur) + 1;
        w.size(d);
    }
};

const Fp128 = field.Fp128;

const fixtures = @import("testing.zig");

test "deserialize the s-gonal test vector" {
    const gpa = std.testing.allocator;
    var c = try Circuit(Fp128).fromBytes(gpa, &fixtures.sgonal_vector_bytes, false);
    defer c.deinit(gpa);

    try std.testing.expectEqual(1, c.nv);
    try std.testing.expectEqual(1, c.nc);
    try std.testing.expectEqual(2, c.npub_in);
    try std.testing.expectEqual(4, c.ninputs);
    try std.testing.expectEqual(2, c.layers.len);
    try std.testing.expectEqual(4, c.constants.len);

    const p = Fp128.modulus;
    try std.testing.expect(c.constants[0].eql(Fp128.fromInt(p - 2)));
    try std.testing.expect(c.constants[1].eql(Fp128.fromInt(p - 1)));
    try std.testing.expect(c.constants[2].eql(Fp128.fromInt(1)));
    try std.testing.expect(c.constants[3].eql(Fp128.fromInt(p - 4)));

    try std.testing.expectEqual(3, c.layers[0].logw);
    try std.testing.expectEqual(6, c.layers[0].nw);
    try std.testing.expectEqual(3, c.layers[0].quads.len);
    try std.testing.expectEqual(2, c.layers[1].logw);
    try std.testing.expectEqual(4, c.layers[1].nw);
    try std.testing.expectEqual(8, c.layers[1].quads.len);
}

test "evaluate the s-gonal circuit" {
    const gpa = std.testing.allocator;
    var c = try Circuit(Fp128).fromBytes(gpa, &fixtures.sgonal_vector_bytes, false);
    defer c.deinit(gpa);

    // 45 is the 5th hexagonal number: 2*45 = (6-2)*25 - (6-4)*5.
    const good = [4]Fp128{ .fromInt(1), .fromInt(45), .fromInt(5), .fromInt(6) };
    const wires = try c.evaluate(gpa, &good);
    defer Circuit(Fp128).freeWires(gpa, wires);
    try std.testing.expectEqual(3, wires.len);
    try std.testing.expect(wires[0][0].isZero());

    // 44 is not hexagonal, so the output must be nonzero.
    const bad = [4]Fp128{ .fromInt(1), .fromInt(44), .fromInt(5), .fromInt(6) };
    const bad_wires = try c.evaluate(gpa, &bad);
    defer Circuit(Fp128).freeWires(gpa, bad_wires);
    try std.testing.expect(!bad_wires[0][0].isZero());
}

test "serialization round trip with id enforcement" {
    const gpa = std.testing.allocator;
    const bytes = &fixtures.sgonal_vector_bytes;
    var c = try Circuit(Fp128).fromBytes(gpa, bytes, false);
    defer c.deinit(gpa);

    c.id = c.computeId();
    const buf = try gpa.alloc(u8, c.serializedSize());
    defer gpa.free(buf);
    const serialized = c.toBytes(buf);
    try std.testing.expectEqual(buf.len, serialized.len);

    // Everything but the spliced-in id must match the adapted vector.
    try std.testing.expectEqualSlices(u8, bytes[0 .. bytes.len - id_len], serialized[0 .. serialized.len - id_len]);

    var c2 = try Circuit(Fp128).fromBytes(gpa, serialized, true);
    defer c2.deinit(gpa);
    try std.testing.expectEqual(c.layers.len, c2.layers.len);

    // Tampering with the id must be caught when enforcement is on.
    serialized[serialized.len - 1] ^= 1;
    try std.testing.expectError(error.IdMismatch, Circuit(Fp128).fromBytes(gpa, serialized, true));
}
