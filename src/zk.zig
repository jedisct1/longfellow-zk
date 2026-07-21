//! The complete Longfellow zero-knowledge argument.
//!
//! A proof that C(x, w) = 0 is assembled from the two sub-protocols: the
//! prover commits (Ligero) to the private inputs followed by a random
//! one-time pad, runs the pad-encrypted sumcheck over the circuit, and
//! then proves with Ligero that the linear and quadratic constraints
//! derived from the encrypted transcript hold for the committed vector.
//!
//! Transcript layout, in order: the Ligero commitment root, the circuit
//! identifier, the public inputs, a pro-forma zero output, one zero byte
//! per circuit term (correlation-intractability padding), the sumcheck
//! messages, and finally the Ligero proof messages.
//! The byte format of a serialized proof matches the reference
//! implementation.

const std = @import("std");
const Allocator = std.mem.Allocator;
const assert = std.debug.assert;

const circuit_mod = @import("circuit.zig");
const sumcheck_mod = @import("sumcheck.zig");
const ligero_mod = @import("ligero.zig");
const Transcript = @import("Transcript.zig");
const MerkleTree = @import("MerkleTree.zig");
const Gf2_128 = @import("Gf2_128.zig");

pub const Digest = MerkleTree.Digest;

/// The reference implementation binds the Ligero statement with this
/// fixed hash; any constant is sound here because the last prover message
/// is already in the transcript.
pub const hash_of_a: Digest = .{ 0xde, 0xad, 0xbe, 0xef } ++ @as([28]u8, @splat(0));

pub const ProveError = error{
    NotSatisfied,
    UnsupportedCopies,
    WrongInputCount,
    InvalidParam,
} || Allocator.Error;

pub const VerifyError = ligero_mod.VerifyError || error{InvalidParam};

pub const DeserializeError = error{MalformedProof} || Allocator.Error;

pub fn Zk(comptime F: type) type {
    return struct {
        pub const Circuit = circuit_mod.Circuit(F);
        pub const Sumcheck = sumcheck_mod.Sumcheck(F);
        pub const Ligero = ligero_mod.Ligero(F);

        /// Commitment-scheme parameters.
        /// `block_enc` is the row length of the Ligero tableau and must
        /// satisfy the constraints of `Ligero.Param.init` for this
        /// circuit's witness size.
        pub const Parameters = struct {
            rateinv: usize = 4,
            nreq: usize,
            block_enc: usize,
        };

        pub const Proof = struct {
            com: Ligero.Commitment,
            sc: Sumcheck.Proof,
            lp: Ligero.Proof,

            pub fn deinit(p: *Proof, gpa: Allocator) void {
                p.sc.deinit(gpa);
                p.lp.deinit(gpa);
                p.* = undefined;
            }
        };

        pub fn ligeroParam(c: Circuit, prm: Parameters) error{InvalidParam}!Ligero.Param {
            const nw = (c.ninputs - c.npub_in) + Sumcheck.padLength(c);
            return Ligero.Param.init(nw, c.layers.len, prm.rateinv, prm.nreq, prm.block_enc);
        }

        /// Produces a proof that the circuit evaluates to zero on
        /// `inputs` (public inputs first).
        /// The transcript must be initialized with the session identifier.
        pub fn prove(
            gpa: Allocator,
            c: Circuit,
            inputs: []const F,
            t: *Transcript,
            prm: Parameters,
            random: std.Random,
        ) ProveError!Proof {
            const par = try ligeroParam(c, prm);
            const n_priv = c.ninputs - c.npub_in;
            if (inputs.len != c.ninputs) return error.WrongInputCount;

            // The witness vector is the private inputs followed by the
            // pad; the pad is generated in place in its tail.
            const witness = try gpa.alloc(F, n_priv + Sumcheck.padLength(c));
            defer gpa.free(witness);
            @memcpy(witness[0..n_priv], inputs[c.npub_in..]);
            const pad = Sumcheck.Pad.generate(witness[n_priv..], c, random);

            const lqc = try Sumcheck.quadraticConstraints(gpa, c);
            defer gpa.free(lqc);

            const boundary = c.subfield_boundary -| c.npub_in;

            var prover = try Ligero.Prover.init(gpa, par);
            defer prover.deinit(gpa);
            const com = prover.commit(t, witness, boundary, lqc, random);

            initializeFiatShamir(t, c, inputs[0..c.npub_in]);

            const wires = c.evaluate(gpa, inputs) catch |err| switch (err) {
                error.AssertionFailed => return error.NotSatisfied,
                else => |e| return e,
            };
            defer Circuit.freeWires(gpa, wires);
            for (wires[0]) |v| {
                if (!v.isZero()) return error.NotSatisfied;
            }

            // The padded sumcheck and the constraint replay perform the
            // same transcript operations; run the former on a copy so the
            // Ligero proof continues from the constraint thread.
            var tsc = t.*;
            var sc = try Sumcheck.prove(gpa, &tsc, c, wires, pad);
            errdefer sc.deinit(gpa);

            var cs = try Sumcheck.constraints(gpa, t, c, inputs[0..c.npub_in], sc);
            defer cs.deinit(gpa);
            var conv = try convertConstraints(gpa, cs);
            defer conv.deinit(gpa);

            const lp = try prover.prove(gpa, t, cs.linear.len, conv.terms, hash_of_a, lqc);
            return .{ .com = com, .sc = sc, .lp = lp };
        }

        /// Verifies a proof against the public inputs.
        /// The transcript must be initialized exactly as the prover's.
        pub fn verify(
            gpa: Allocator,
            c: Circuit,
            public_inputs: []const F,
            proof: Proof,
            t: *Transcript,
            prm: Parameters,
        ) VerifyError!void {
            const par = try ligeroParam(c, prm);
            assert(public_inputs.len == c.npub_in);

            t.writeBytes(&proof.com.root);
            initializeFiatShamir(t, c, public_inputs);

            var cs = try Sumcheck.constraints(gpa, t, c, public_inputs, proof.sc);
            defer cs.deinit(gpa);
            var conv = try convertConstraints(gpa, cs);
            defer conv.deinit(gpa);

            try Ligero.verify(gpa, par, proof.com, proof.lp, t, conv.terms, hash_of_a, conv.b, cs.quadratic);
        }

        fn initializeFiatShamir(t: *Transcript, c: Circuit, public_inputs: []const F) void {
            t.writeBytes(&c.id);
            for (public_inputs) |x| t.writeField(F, x);
            t.writeField(F, F.zero);
            t.writeZeros(c.numTerms());
        }

        const ConvertedConstraints = struct {
            terms: []Ligero.LinearTerm,
            b: []F,

            fn deinit(cc: *ConvertedConstraints, gpa: Allocator) void {
                gpa.free(cc.terms);
                gpa.free(cc.b);
                cc.* = undefined;
            }
        };

        /// Rewrites "k + sum(coeff*w) = 0" constraints into the sparse
        /// A*w = b form Ligero consumes.
        fn convertConstraints(gpa: Allocator, cs: Sumcheck.Constraints) Allocator.Error!ConvertedConstraints {
            var total: usize = 0;
            for (cs.linear) |lc| total += lc.terms.len;
            const terms = try gpa.alloc(Ligero.LinearTerm, total);
            errdefer gpa.free(terms);
            const b = try gpa.alloc(F, cs.linear.len);
            errdefer gpa.free(b);

            var k: usize = 0;
            for (cs.linear, b, 0..) |lc, *bv, ci| {
                bv.* = lc.k.neg();
                for (lc.terms) |term| {
                    terms[k] = .{ .c = ci, .w = term.index, .k = term.coeff };
                    k += 1;
                }
            }
            return .{ .terms = terms, .b = b };
        }

        /// Byte length of the serialized proof.
        pub fn proofSize(c: Circuit, proof: Proof) usize {
            var n: usize = proof.com.root.len;
            for (c.layers) |layer| n += (4 * layer.logw + 2) * F.encoded_len;
            n += (proof.lp.y_ldt.len + proof.lp.y_dot.len +
                proof.lp.y_quad_0.len + proof.lp.y_quad_2.len) * F.encoded_len;
            n += proof.lp.nonces.len * ligero_mod.nonce_len;

            const req = proof.lp.req;
            var ci: usize = 0;
            var subfield_run = false;
            while (ci < req.len) {
                const runlen = runLength(req, ci, subfield_run);
                n += size_bytes + runlen *
                    @as(usize, if (subfield_run) F.subfield_encoded_len else F.encoded_len);
                ci += runlen;
                subfield_run = !subfield_run;
            }

            return n + size_bytes + proof.lp.path.len * @sizeOf(Digest);
        }

        /// Serializes a proof in the reference byte format: commitment
        /// root, sumcheck proof, then the Ligero proof with run-length
        /// encoded opened columns.
        /// `out` must hold at least proofSize(c, proof) bytes; the used
        /// prefix is returned.
        pub fn proofToBytes(c: Circuit, proof: Proof, out: []u8) []u8 {
            var w: Writer = .{ .out = out };

            w.bytes(&proof.com.root);

            for (c.layers, proof.sc.layers) |layer, lp| {
                for (0..layer.logw) |wi| {
                    w.bytes(&lp.evals[2 * wi].p0.toBytes());
                    w.bytes(&lp.evals[2 * wi + 1].p0.toBytes());
                    w.bytes(&lp.evals[2 * wi].p2.toBytes());
                    w.bytes(&lp.evals[2 * wi + 1].p2.toBytes());
                }
                w.bytes(&lp.vl.toBytes());
                w.bytes(&lp.vr.toBytes());
            }

            for (proof.lp.y_ldt) |e| w.bytes(&e.toBytes());
            for (proof.lp.y_dot) |e| w.bytes(&e.toBytes());
            for (proof.lp.y_quad_0) |e| w.bytes(&e.toBytes());
            for (proof.lp.y_quad_2) |e| w.bytes(&e.toBytes());
            for (proof.lp.nonces) |n| w.bytes(&n);

            // Opened columns as alternating runs of full-field and
            // subfield encodings, starting with a full-field run.
            const req = proof.lp.req;
            var ci: usize = 0;
            var subfield_run = false;
            while (ci < req.len) {
                const runlen = runLength(req, ci, subfield_run);
                w.size(runlen);
                for (req[ci..][0..runlen]) |e| {
                    if (subfield_run) {
                        w.bytes(&e.toSubfieldBytes().?);
                    } else {
                        w.bytes(&e.toBytes());
                    }
                }
                ci += runlen;
                subfield_run = !subfield_run;
            }

            w.size(proof.lp.path.len);
            for (proof.lp.path) |d| w.bytes(&d);

            return out[0..w.pos];
        }

        /// Length of the run of opened-column entries at `start` whose
        /// membership in the subfield matches the current run kind.
        fn runLength(req: []const F, start: usize, subfield_run: bool) usize {
            var len: usize = 0;
            while (start + len < req.len and len < max_run_len and
                req[start + len].isInSubfield() == subfield_run) : (len += 1)
            {}
            return len;
        }

        pub fn proofFromBytes(gpa: Allocator, c: Circuit, par: Ligero.Param, bytes: []const u8) DeserializeError!Proof {
            var r: Reader = .{ .bytes = bytes };

            const root = try r.digest();

            var total_evals: usize = 0;
            for (c.layers) |layer| total_evals += 2 * layer.logw;
            const evals_pool = try gpa.alloc(Sumcheck.Poly, total_evals);
            errdefer gpa.free(evals_pool);
            const sc_layers = try gpa.alloc(Sumcheck.LayerProof, c.layers.len);
            errdefer gpa.free(sc_layers);
            var off: usize = 0;
            for (c.layers, sc_layers) |layer, *lp| {
                const evals = evals_pool[off..][0 .. 2 * layer.logw];
                off += evals.len;
                lp.evals = evals;
                for (0..layer.logw) |wi| {
                    evals[2 * wi].p0 = try r.elt();
                    evals[2 * wi + 1].p0 = try r.elt();
                    evals[2 * wi].p2 = try r.elt();
                    evals[2 * wi + 1].p2 = try r.elt();
                }
                lp.vl = try r.elt();
                lp.vr = try r.elt();
            }

            const y_ldt = try gpa.alloc(F, par.block);
            errdefer gpa.free(y_ldt);
            for (y_ldt) |*e| e.* = try r.elt();
            const y_dot = try gpa.alloc(F, par.dblock);
            errdefer gpa.free(y_dot);
            for (y_dot) |*e| e.* = try r.elt();
            const y_quad_0 = try gpa.alloc(F, par.nreq);
            errdefer gpa.free(y_quad_0);
            for (y_quad_0) |*e| e.* = try r.elt();
            const y_quad_2 = try gpa.alloc(F, par.dblock - par.block);
            errdefer gpa.free(y_quad_2);
            for (y_quad_2) |*e| e.* = try r.elt();

            const nonces = try gpa.alloc([ligero_mod.nonce_len]u8, par.nreq);
            errdefer gpa.free(nonces);
            for (nonces) |*n| n.* = try r.digest();

            const req = try gpa.alloc(F, par.nrow * par.nreq);
            errdefer gpa.free(req);
            var ci: usize = 0;
            var subfield_run = false;
            while (ci < req.len) {
                const runlen = try r.size();
                if (runlen > max_run_len or ci + runlen > req.len) return error.MalformedProof;
                for (req[ci..][0..runlen]) |*e| {
                    e.* = if (subfield_run) try r.subfieldElt() else try r.elt();
                }
                ci += runlen;
                subfield_run = !subfield_run;
            }

            const path_len = try r.size();
            const max_path = par.nreq * MerkleTree.maxProofLen(par.block_ext);
            if (path_len < par.nreq or path_len > max_path) return error.MalformedProof;
            const path = try gpa.alloc(Digest, path_len);
            errdefer gpa.free(path);
            for (path) |*d| d.* = try r.digest();

            if (r.pos != bytes.len) return error.MalformedProof;

            return .{
                .com = .{ .root = root },
                .sc = .{ .evals = evals_pool, .layers = sc_layers },
                .lp = .{
                    .y_ldt = y_ldt,
                    .y_dot = y_dot,
                    .y_quad_0 = y_quad_0,
                    .y_quad_2 = y_quad_2,
                    .req = req,
                    .nonces = nonces,
                    .path = path,
                },
            };
        }

        const max_run_len = 1 << 25;
        const size_bytes = 4;

        const Writer = struct {
            out: []u8,
            pos: usize = 0,

            fn bytes(w: *Writer, b: []const u8) void {
                @memcpy(w.out[w.pos..][0..b.len], b);
                w.pos += b.len;
            }

            fn size(w: *Writer, v: usize) void {
                assert(v <= std.math.maxInt(u32));
                std.mem.writeInt(u32, w.out[w.pos..][0..size_bytes], @intCast(v), .little);
                w.pos += size_bytes;
            }
        };

        const Reader = struct {
            bytes: []const u8,
            pos: usize = 0,

            fn take(r: *Reader, comptime n: usize) DeserializeError![n]u8 {
                if (r.bytes.len - r.pos < n) return error.MalformedProof;
                defer r.pos += n;
                return r.bytes[r.pos..][0..n].*;
            }

            fn elt(r: *Reader) DeserializeError!F {
                return F.fromBytes(try r.take(F.encoded_len)) catch error.MalformedProof;
            }

            fn subfieldElt(r: *Reader) DeserializeError!F {
                const b = try r.take(F.subfield_encoded_len);
                return F.fromSubfieldBytes(b) catch error.MalformedProof;
            }

            fn digest(r: *Reader) DeserializeError![32]u8 {
                return r.take(32);
            }

            fn size(r: *Reader) DeserializeError!usize {
                const b = try r.take(4);
                return std.mem.readInt(u32, &b, .little);
            }
        };
    };
}

const Fp128 = @import("field.zig").Fp128;
const fixtures = @import("testing.zig");
const sgonalCircuit = fixtures.sgonalCircuit;

test "end-to-end prove and verify" {
    const gpa = std.testing.allocator;
    const Z = Zk(Fp128);

    var c = try sgonalCircuit(gpa);
    defer c.deinit(gpa);

    // Witness length is 2 private inputs + 26 pad elements = 28.
    const prm: Z.Parameters = .{ .nreq = 6, .block_enc = 128 };
    const inputs = fixtures.sgonal_inputs;
    var prng = std.Random.DefaultPrng.init(1);

    var tp = Transcript.init("zk test");
    var proof = try Z.prove(gpa, c, &inputs, &tp, prm, prng.random());
    defer proof.deinit(gpa);

    var tv = Transcript.init("zk test");
    try Z.verify(gpa, c, inputs[0..2], proof, &tv, prm);

    // Different public inputs diverge the transcript and must fail.
    const bad_pub = [2]Fp128{ .fromInt(1), .fromInt(44) };
    var tb = Transcript.init("zk test");
    try std.testing.expectError(
        error.MerkleCheckFailed,
        Z.verify(gpa, c, &bad_pub, proof, &tb, prm),
    );

    // A different session id must fail as well.
    var ts = Transcript.init("other session");
    try std.testing.expectError(
        error.MerkleCheckFailed,
        Z.verify(gpa, c, inputs[0..2], proof, &ts, prm),
    );
}

test "proving an unsatisfied statement fails" {
    const gpa = std.testing.allocator;
    const Z = Zk(Fp128);

    var c = try sgonalCircuit(gpa);
    defer c.deinit(gpa);

    const prm: Z.Parameters = .{ .nreq = 6, .block_enc = 128 };
    const inputs = [4]Fp128{ .fromInt(1), .fromInt(44), .fromInt(5), .fromInt(6) };
    var prng = std.Random.DefaultPrng.init(2);

    var tp = Transcript.init("zk test");
    try std.testing.expectError(
        error.NotSatisfied,
        Z.prove(gpa, c, &inputs, &tp, prm, prng.random()),
    );
}

test "proof serialization round trip" {
    const gpa = std.testing.allocator;
    const Z = Zk(Fp128);

    var c = try sgonalCircuit(gpa);
    defer c.deinit(gpa);

    const prm: Z.Parameters = .{ .nreq = 6, .block_enc = 128 };
    const par = try Z.ligeroParam(c, prm);
    const inputs = fixtures.sgonal_inputs;
    var prng = std.Random.DefaultPrng.init(3);

    var tp = Transcript.init("zk serialization test");
    var proof = try Z.prove(gpa, c, &inputs, &tp, prm, prng.random());
    defer proof.deinit(gpa);

    const buf = try gpa.alloc(u8, Z.proofSize(c, proof));
    defer gpa.free(buf);
    const bytes = Z.proofToBytes(c, proof, buf);
    try std.testing.expectEqual(buf.len, bytes.len);

    var decoded = try Z.proofFromBytes(gpa, c, par, bytes);
    defer decoded.deinit(gpa);

    const buf2 = try gpa.alloc(u8, Z.proofSize(c, decoded));
    defer gpa.free(buf2);
    const bytes2 = Z.proofToBytes(c, decoded, buf2);
    try std.testing.expectEqualSlices(u8, bytes, bytes2);

    var tv = Transcript.init("zk serialization test");
    try Z.verify(gpa, c, inputs[0..2], decoded, &tv, prm);

    // Truncation is rejected.
    try std.testing.expectError(
        error.MalformedProof,
        Z.proofFromBytes(gpa, c, par, bytes[0 .. bytes.len - 1]),
    );
}

test "end-to-end over GF(2^128)" {
    const gpa = std.testing.allocator;
    const Z = Zk(Gf2_128);
    const C = circuit_mod.Circuit(Gf2_128);

    // A hand-built circuit checking w1*w2 = w3 (with public constant-one
    // wire w0): the single output is 1*w1*w2 + 1*w0*w3, which is zero in
    // characteristic two exactly when w1*w2 = w3.
    const constants = try gpa.dupe(Gf2_128, &.{Gf2_128.one});
    const quads = try gpa.dupe(C.Quad, &.{
        .{ .g = 0, .h0 = 1, .h1 = 2, .v = 0 },
        .{ .g = 0, .h0 = 0, .h1 = 3, .v = 0 },
    });
    const layers = try gpa.alloc(C.Layer, 1);
    layers[0] = .{ .logw = 2, .nw = 4, .quads = quads };
    var c: C = .{
        .nv = 1,
        .nc = 1,
        .npub_in = 1,
        .subfield_boundary = 4,
        .ninputs = 4,
        .constants = constants,
        .layers = layers,
        .id = undefined,
    };
    defer c.deinit(gpa);
    c.id = c.computeId();

    const a = Gf2_128.inj(333);
    const b = Gf2_128.inj(4711);
    const inputs = [4]Gf2_128{ Gf2_128.one, a, b, a.mul(b) };

    const prm: Z.Parameters = .{ .nreq = 3, .block_enc = 64 };
    var prng = std.Random.DefaultPrng.init(4);

    var tp = Transcript.init("zk gf2 test");
    var proof = try Z.prove(gpa, c, &inputs, &tp, prm, prng.random());
    defer proof.deinit(gpa);

    var tv = Transcript.init("zk gf2 test");
    try Z.verify(gpa, c, inputs[0..1], proof, &tv, prm);

    // Serialization round trip, exercising the subfield run encoding.
    const par = try Z.ligeroParam(c, prm);
    const buf = try gpa.alloc(u8, Z.proofSize(c, proof));
    defer gpa.free(buf);
    const bytes = Z.proofToBytes(c, proof, buf);
    try std.testing.expectEqual(buf.len, bytes.len);
    var decoded = try Z.proofFromBytes(gpa, c, par, bytes);
    defer decoded.deinit(gpa);
    var tv2 = Transcript.init("zk gf2 test");
    try Z.verify(gpa, c, inputs[0..1], decoded, &tv2, prm);
}
