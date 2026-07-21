//! Prime-order finite fields used by the Longfellow ZK system.
//!
//! Every field is an instantiation of `PrimeField`, a thin wrapper around
//! `std.crypto.ff` that fixes the modulus at compile time and keeps elements
//! in Montgomery form between the byte-serialization boundaries.

const std = @import("std");
const ff = std.crypto.ff;
const Gf2_128 = @import("Gf2_128.zig");

/// Field identifiers from the circuit serialization format.
pub const FieldId = enum(u8) {
    /// Base field of the NIST P-256 curve.
    p256 = 0x01,
    /// Base field of the NIST P-384 curve.
    p384 = 0x02,
    /// 2^521 - 1, base field of the NIST P-521 curve.
    p521 = 0x03,
    /// GF(2)[x] / (x^128 + x^7 + x^2 + x + 1).
    gf2_128 = 0x04,
    /// The subfield of GF(2^128) with 2^16 elements.
    gf2_16 = 0x05,
    /// 2^128 - 2^108 + 1.
    fp128 = 0x06,
    /// 2^64 - 59.
    fp64 = 0x07,
    /// 2^64 - 2^32 + 1.
    goldilocks = 0x08,
    /// Quadratic extension of F_{2^64 - 59} by x^2 + 1.
    fp64_2 = 0x09,
    /// Base field of the secp256k1 curve.
    secp256k1 = 0x0a,
    _,
};

/// Maps a field type to its serialization identifier.
pub fn fieldIdOf(comptime F: type) FieldId {
    if (F == Fp128) return .fp128;
    if (F == Fp256) return .p256;
    if (F == Secp256k1) return .secp256k1;
    if (F == Gf2_128) return .gf2_128;
    @compileError("no field identifier for " ++ @typeName(F));
}

/// The prime field Z/(p) for an odd modulus `p` known at compile time.
///
/// The returned struct is the field element itself; arithmetic never
/// allocates and elements are plain values.
/// Serialization is little-endian over `encoded_len` bytes and rejects
/// non-canonical encodings, which is also the rejection-sampling test the
/// Fiat-Shamir transcript relies on.
pub fn PrimeField(comptime p: comptime_int) type {
    const bit_count = std.math.log2(p) + 1;
    const M = ff.Modulus(bit_count);
    const T = @Int(.unsigned, bit_count);

    return struct {
        fe: M.Fe,

        const Fe = @This();

        pub const modulus = p;
        pub const bits = bit_count;
        pub const encoded_len = @divCeil(bits, 8);
        /// Largest usable `extend` domain: the canonical points 0, 1, ...
        /// repeat modulo p beyond this.
        pub const extend_domain_limit: usize = @min(p, std.math.maxInt(usize));
        /// Sumcheck evaluation point P2, which is 2 in odd-characteristic
        /// fields.
        pub const p2: Fe = .fromInt(2);

        const m = blk: {
            @setEvalBranchQuota(1_000_000);
            break :blk M.fromPrimitive(T, p) catch unreachable;
        };

        pub const zero: Fe = .{
            .fe = blk: {
                @setEvalBranchQuota(1_000_000);
                var z = M.Fe.fromPrimitive(T, m, 0) catch unreachable;
                // Zero is its own Montgomery form; only the flag needs fixing
                // so that all elements share one representation.
                z.montgomery = true;
                break :blk z;
            },
        };
        pub const one: Fe = .fromInt(1);

        /// Converts an integer below the modulus into a field element.
        pub fn fromInt(x: T) Fe {
            @setEvalBranchQuota(1_000_000);
            std.debug.assert(x < p);
            var e = M.Fe.fromPrimitive(T, m, x) catch unreachable;
            m.toMontgomery(&e) catch unreachable;
            return .{ .fe = e };
        }

        pub fn toInt(a: Fe) T {
            var e = a.fe;
            m.fromMontgomery(&e) catch unreachable;
            return e.toPrimitive(T) catch unreachable;
        }

        /// Decodes a canonical little-endian encoding.
        pub fn fromBytes(bytes: [encoded_len]u8) error{NonCanonical}!Fe {
            var e = M.Fe.fromBytes(m, &bytes, .little) catch return error.NonCanonical;
            m.toMontgomery(&e) catch unreachable;
            return .{ .fe = e };
        }

        pub fn toBytes(a: Fe) [encoded_len]u8 {
            var e = a.fe;
            m.fromMontgomery(&e) catch unreachable;
            var out: [encoded_len]u8 = undefined;
            e.toBytes(&out, .little) catch unreachable;
            return out;
        }

        /// Subfield interface shared with the binary fields.
        /// A prime field is its own subfield, so these alias the
        /// full-field encoding and every element qualifies.
        pub const subfield_encoded_len = encoded_len;

        pub fn isInSubfield(a: Fe) bool {
            _ = a;
            return true;
        }

        pub fn toSubfieldBytes(a: Fe) ?[subfield_encoded_len]u8 {
            return a.toBytes();
        }

        pub fn fromSubfieldBytes(bytes: [subfield_encoded_len]u8) error{NonCanonical}!Fe {
            return fromBytes(bytes);
        }

        /// Uniformly random element, by rejection sampling on the
        /// canonical encoding.
        pub fn random(rand: std.Random) Fe {
            while (true) {
                var b: [encoded_len]u8 = undefined;
                rand.bytes(&b);
                return fromBytes(b) catch continue;
            }
        }

        pub fn randomSubfield(rand: std.Random) Fe {
            return random(rand);
        }

        pub fn add(a: Fe, b: Fe) Fe {
            return .{ .fe = m.add(a.fe, b.fe) };
        }

        pub fn sub(a: Fe, b: Fe) Fe {
            return .{ .fe = m.sub(a.fe, b.fe) };
        }

        pub fn neg(a: Fe) Fe {
            return zero.sub(a);
        }

        pub fn mul(a: Fe, b: Fe) Fe {
            return .{ .fe = m.mul(a.fe, b.fe) };
        }

        pub fn square(a: Fe) Fe {
            return .{ .fe = m.sq(a.fe) };
        }

        /// Multiplicative inverse, or null for zero.
        pub fn invert(a: Fe) ?Fe {
            const inv = m.invertPublic(a.fe) orelse return null;
            return .{ .fe = inv };
        }

        pub fn eql(a: Fe, b: Fe) bool {
            return a.fe.eql(b.fe);
        }

        pub fn isZero(a: Fe) bool {
            return a.fe.isZero();
        }

        /// Scratch length `extend` requires for a basis of `flen`
        /// evaluations; prime fields need none.
        pub fn extendScratchLen(flen: usize) usize {
            _ = flen;
            return 0;
        }

        /// The `extend` operation from the specification: interprets `f` as
        /// the evaluations of a polynomial of degree < `f.len` at the points
        /// 0, 1, ..., f.len-1 and writes its evaluations at 0, 1, ...,
        /// out.len-1 to `out`.
        ///
        /// Works by extending the forward-difference table of `f`, which
        /// only requires additions.
        /// The table is built in place in `out`'s prefix, so `f` must not
        /// alias `out`.
        ///
        /// Asserts that `f` is not empty.
        pub fn extend(out: []Fe, f: []const Fe, scratch: []Fe) void {
            std.debug.assert(f.len > 0);
            _ = scratch;
            const n = out.len;
            @memcpy(out[0..@min(f.len, n)], f[0..@min(f.len, n)]);
            if (n <= f.len) return;

            const d = out[0..f.len];
            for (1..d.len) |k| {
                var i = d.len - 1;
                while (i >= k) : (i -= 1) d[i] = d[i].sub(d[i - 1]);
            }
            // d[k] is now the k-th forward difference at 0.
            // Stepping the table once advances every difference from x to
            // x + 1, making d[0] the next evaluation.
            for (1..n) |x| {
                for (0..d.len - 1) |k| d[k] = d[k].add(d[k + 1]);
                if (x >= f.len) out[x] = d[0];
            }
            @memcpy(out[0..f.len], f);
        }
    };
}

/// 2^128 - 2^108 + 1, the field used by the specification test vectors.
pub const Fp128 = PrimeField((1 << 128) - (1 << 108) + 1);

/// Base field of the NIST P-256 curve.
pub const Fp256 = PrimeField((1 << 256) - (1 << 224) + (1 << 192) + (1 << 96) - 1);

/// Base field of the secp256k1 curve, used by the Fiat-Shamir test vectors.
pub const Secp256k1 = PrimeField((1 << 256) - (1 << 32) - 977);

test "field arithmetic in Fp128" {
    const F = Fp128;
    const a = F.fromInt(0x123456789abcdef0fedcba9876543210);
    const b = F.fromInt(0xfffffff000000000000000000000001);

    const expected_sum = (0x123456789abcdef0fedcba9876543210 + 0xfffffff000000000000000000000001) % F.modulus;
    try std.testing.expectEqual(expected_sum, a.add(b).toInt());

    const expected_prod = (0x123456789abcdef0fedcba9876543210 * 0xfffffff000000000000000000000001) % F.modulus;
    try std.testing.expectEqual(expected_prod, a.mul(b).toInt());

    try std.testing.expect(a.sub(b).add(b).eql(a));
    try std.testing.expect(a.mul(b).eql(b.mul(a)));
    try std.testing.expect(a.square().eql(a.mul(a)));
    try std.testing.expect(a.neg().add(a).isZero());
    try std.testing.expect(F.one.mul(a).eql(a));
    try std.testing.expect(F.zero.add(a).eql(a));

    const inv = a.invert().?;
    try std.testing.expect(inv.mul(a).eql(F.one));
    try std.testing.expect(F.zero.invert() == null);
}

test "field serialization round trip" {
    const F = Fp128;
    const a = F.fromInt(0xdeadbeefcafebabe0123456789abcdef);
    const bytes = a.toBytes();
    try std.testing.expectEqual(a.toInt(), (try F.fromBytes(bytes)).toInt());

    var noncanonical: [F.encoded_len]u8 = undefined;
    std.mem.writeInt(u128, &noncanonical, F.modulus, .little);
    try std.testing.expectError(error.NonCanonical, F.fromBytes(noncanonical));

    var largest: [F.encoded_len]u8 = undefined;
    std.mem.writeInt(u128, &largest, F.modulus - 1, .little);
    try std.testing.expectEqual(F.modulus - 1, (try F.fromBytes(largest)).toInt());
}

test "extend reproduces polynomial evaluations" {
    const F = Fp128;

    // P(x) = 3x^2 + 2x + 7 evaluated at 0..3, extended to 0..9.
    var f: [4]F = undefined;
    for (&f, 0..) |*e, x| e.* = F.fromInt(3 * x * x + 2 * x + 7);
    var ext: [10]F = undefined;
    F.extend(&ext, &f, &.{});
    for (ext, 0..) |e, x| {
        try std.testing.expectEqual(3 * x * x + 2 * x + 7, e.toInt());
    }

    // Extending to fewer points is a prefix copy.
    var short: [2]F = undefined;
    F.extend(&short, &f, &.{});
    try std.testing.expectEqual(7, short[0].toInt());
    try std.testing.expectEqual(12, short[1].toInt());
}

test "extend matches Lagrange interpolation in Secp256k1" {
    const F = Secp256k1;

    var f: [3]F = .{ F.fromInt(11), F.fromInt(22), F.fromInt(44) };
    var ext: [6]F = undefined;
    F.extend(&ext, &f, &.{});

    // Evaluate the interpolation directly at x = 5 for a cross-check:
    // P(x) = 11*L0 + 22*L1 + 44*L2 over points 0,1,2.
    const x = F.fromInt(5);
    const l0 = x.sub(F.fromInt(1)).mul(x.sub(F.p2)).mul(F.p2.invert().?);
    const l1 = x.mul(x.sub(F.p2)).mul(F.one.neg().invert().?);
    const l2 = x.mul(x.sub(F.one)).mul(F.p2.invert().?);
    const want = F.fromInt(11).mul(l0).add(F.fromInt(22).mul(l1)).add(F.fromInt(44).mul(l2));
    try std.testing.expect(ext[5].eql(want));
}
