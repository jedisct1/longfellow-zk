//! The binary field GF(2^128) = GF(2)[x] / (x^128 + x^7 + x^2 + x + 1),
//! together with its GF(2^16) subfield.
//!
//! An element stores the coefficient of x^i in bit i of `v`, so the byte
//! serialization is simply the little-endian encoding of `v`.
//! With this modulus, x generates the multiplicative group.
//! The subfield is spanned by the basis beta_i = g^i for 0 <= i < 16 where
//! g = x^((2^128-1)/(2^16-1)), and `inj` maps an integer to a field element
//! by using its bits as coordinates in that basis.
//! Because `inj` is GF(2)-linear, inj(a) + inj(b) = inj(a xor b), which the
//! `extend` implementation relies on.

const std = @import("std");
const assert = std.debug.assert;

v: u128,

const Gf2_128 = @This();

pub const bits = 128;
pub const encoded_len = 16;
pub const subfield_encoded_len = 2;
/// Largest usable `extend` domain: `inj` is only defined on 16-bit
/// integers.
pub const extend_domain_limit: usize = 1 << 16;

pub const zero: Gf2_128 = .{ .v = 0 };
pub const one: Gf2_128 = .{ .v = 1 };

/// Generator of the multiplicative group of the GF(2^16) subfield.
pub const g: Gf2_128 = blk: {
    @setEvalBranchQuota(10_000_000);
    const x: Gf2_128 = .{ .v = 2 };
    break :blk x.pow(((1 << 128) - 1) / ((1 << 16) - 1));
};

/// Basis of the GF(2^16) subfield: beta[i] = g^i.
pub const beta: [16]Gf2_128 = blk: {
    @setEvalBranchQuota(10_000_000);
    var b: [16]Gf2_128 = undefined;
    b[0] = one;
    for (1..16) |i| b[i] = b[i - 1].mul(g);
    break :blk b;
};

/// Sumcheck evaluation point P2 = inj(2).
pub const p2: Gf2_128 = beta[1];

pub fn fromInt(x: u128) Gf2_128 {
    return .{ .v = x };
}

pub fn toInt(a: Gf2_128) u128 {
    return a.v;
}

/// Decodes the 128 bits of `bytes` as a little-endian polynomial.
/// Never actually fails; the error set matches the prime fields so that
/// generic rejection-sampling code can treat all fields alike.
pub fn fromBytes(bytes: [encoded_len]u8) error{NonCanonical}!Gf2_128 {
    return .{ .v = std.mem.readInt(u128, &bytes, .little) };
}

pub fn toBytes(a: Gf2_128) [encoded_len]u8 {
    var out: [encoded_len]u8 = undefined;
    std.mem.writeInt(u128, &out, a.v, .little);
    return out;
}

pub fn add(a: Gf2_128, b: Gf2_128) Gf2_128 {
    return .{ .v = a.v ^ b.v };
}

/// In characteristic 2, subtraction and addition coincide.
pub fn sub(a: Gf2_128, b: Gf2_128) Gf2_128 {
    return a.add(b);
}

pub fn neg(a: Gf2_128) Gf2_128 {
    return a;
}

pub fn mul(a: Gf2_128, b: Gf2_128) Gf2_128 {
    const lo_a: u64 = @truncate(a.v);
    const hi_a: u64 = @truncate(a.v >> 64);
    const lo_b: u64 = @truncate(b.v);
    const hi_b: u64 = @truncate(b.v >> 64);

    // Karatsuba over the 64-bit halves.
    const lo = clmul64(lo_a, lo_b);
    const hi = clmul64(hi_a, hi_b);
    const mid = clmul64(lo_a ^ hi_a, lo_b ^ hi_b) ^ lo ^ hi;

    return .{ .v = reduce(hi ^ (mid >> 64), lo ^ (mid << 64)) };
}

pub fn square(a: Gf2_128) Gf2_128 {
    return .{ .v = reduce(spread(@truncate(a.v >> 64)), spread(@truncate(a.v))) };
}

pub fn pow(a: Gf2_128, e: u128) Gf2_128 {
    var result = one;
    var base = a;
    var k = e;
    while (k != 0) : (k >>= 1) {
        if (k & 1 != 0) result = result.mul(base);
        base = base.square();
    }
    return result;
}

/// Multiplicative inverse, or null for zero.
pub fn invert(a: Gf2_128) ?Gf2_128 {
    if (a.v == 0) return null;
    return a.pow(std.math.maxInt(u128) - 1);
}

pub fn eql(a: Gf2_128, b: Gf2_128) bool {
    return a.v == b.v;
}

pub fn isZero(a: Gf2_128) bool {
    return a.v == 0;
}

/// Carry-less 32x32 -> 64 multiplication.
/// Splits both operands into four interleaved streams so that ordinary
/// integer multiplications can be used: each output column then
/// accumulates at most 8 one-bits, so the carries stay within the
/// three-bit holes and get masked away.
/// The stream width matters: 64-bit operands would put up to 16 bits in a
/// stream and overflow the holes.
fn clmul32(x: u32, y: u32) u64 {
    const m: u32 = 0x11111111;
    const mw: u64 = 0x1111111111111111;
    var x_p: [4]u32 = undefined;
    var y_p: [4]u32 = undefined;
    for (0..4) |i| {
        x_p[i] = x & (m << @intCast(i));
        y_p[i] = y & (m << @intCast(i));
    }
    var r: u64 = 0;
    for (0..4) |k| {
        var z: u64 = 0;
        for (0..4) |i| {
            const j = (k + 4 - i) % 4;
            z ^= std.math.mulWide(u32, x_p[i], y_p[j]);
        }
        r ^= z & (mw << @intCast(k));
    }
    return r;
}

/// Carry-less 64x64 -> 128 multiplication, Karatsuba over 32-bit halves.
fn clmul64(x: u64, y: u64) u128 {
    const x0: u32 = @truncate(x);
    const x1: u32 = @truncate(x >> 32);
    const y0: u32 = @truncate(y);
    const y1: u32 = @truncate(y >> 32);
    const lo = clmul32(x0, y0);
    const hi = clmul32(x1, y1);
    const mid = clmul32(x0 ^ x1, y0 ^ y1) ^ lo ^ hi;
    return (@as(u128, hi) << 64) ^ (@as(u128, mid) << 32) ^ lo;
}

/// Inserts a zero bit after every bit of `x`, computing the carry-less
/// square of a 64-bit polynomial.
fn spread(x: u64) u128 {
    var r: u128 = x;
    r = (r | (r << 32)) & 0x00000000ffffffff00000000ffffffff;
    r = (r | (r << 16)) & 0x0000ffff0000ffff0000ffff0000ffff;
    r = (r | (r << 8)) & 0x00ff00ff00ff00ff00ff00ff00ff00ff;
    r = (r | (r << 4)) & 0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f;
    r = (r | (r << 2)) & 0x33333333333333333333333333333333;
    r = (r | (r << 1)) & 0x55555555555555555555555555555555;
    return r;
}

/// Reduces a 256-bit carry-less product modulo x^128 + x^7 + x^2 + x + 1.
fn reduce(hi: u128, lo: u128) u128 {
    const r = lo ^ hi ^ (hi << 1) ^ (hi << 2) ^ (hi << 7);
    const o = (hi >> 127) ^ (hi >> 126) ^ (hi >> 121);
    return r ^ o ^ (o << 1) ^ (o << 2) ^ (o << 7);
}

/// Reduced row echelon form of the subfield basis, for extracting subfield
/// coordinates: each entry clears one leading bit, and `combs` tracks which
/// basis elements were combined to produce it.
const echelon = blk: {
    @setEvalBranchQuota(10_000_000);
    var rows: [16]u128 = undefined;
    var combs: [16]u16 = undefined;
    var lead: [16]u7 = undefined;
    var count = 0;
    for (beta, 0..) |b, i| {
        var r = b.v;
        var c: u16 = 1 << i;
        var placed = false;
        while (!placed) {
            const lb = 127 - @clz(r);
            var reduced = false;
            for (0..count) |k| {
                if (lead[k] == lb) {
                    r ^= rows[k];
                    c ^= combs[k];
                    reduced = true;
                    break;
                }
            }
            if (!reduced) {
                rows[count] = r;
                combs[count] = c;
                lead[count] = lb;
                count += 1;
                placed = true;
            }
        }
    }
    // Full reduction, one pivot at a time: once a pivot bit is eliminated
    // from every other row, no later elimination can reintroduce it, so
    // afterwards extraction may process the rows in any order.
    for (0..16) |k| {
        for (0..16) |j| {
            if (j != k and (rows[j] >> lead[k]) & 1 != 0) {
                rows[j] ^= rows[k];
                combs[j] ^= combs[k];
            }
        }
    }
    break :blk .{ .rows = rows, .combs = combs, .lead = lead };
};

/// Maps an integer to a field element by using its bits as coordinates in
/// the subfield basis (the `inj` function of the specification).
pub fn inj(j: u16) Gf2_128 {
    var r: u128 = 0;
    for (beta, 0..) |b, i| {
        if ((j >> @intCast(i)) & 1 != 0) r ^= b.v;
    }
    return .{ .v = r };
}

/// Returns the subfield coordinates of `a`, or null if `a` does not lie in
/// the GF(2^16) subfield.
/// Inverse of `inj`.
pub fn toSubfield(a: Gf2_128) ?u16 {
    var r = a.v;
    var c: u16 = 0;
    for (0..16) |k| {
        if ((r >> echelon.lead[k]) & 1 != 0) {
            r ^= echelon.rows[k];
            c ^= echelon.combs[k];
        }
    }
    return if (r == 0) c else null;
}

pub fn isInSubfield(a: Gf2_128) bool {
    return a.toSubfield() != null;
}

/// Decodes the 16 bits of `bytes` as little-endian subfield coordinates.
/// Never actually fails; the error set matches the prime fields.
pub fn fromSubfieldBytes(bytes: [subfield_encoded_len]u8) error{NonCanonical}!Gf2_128 {
    return inj(std.mem.readInt(u16, &bytes, .little));
}

/// Serializes a subfield element to its 2-byte coordinate encoding, or
/// null if `a` does not lie in the subfield.
pub fn toSubfieldBytes(a: Gf2_128) ?[subfield_encoded_len]u8 {
    const coords = a.toSubfield() orelse return null;
    var out: [subfield_encoded_len]u8 = undefined;
    std.mem.writeInt(u16, &out, coords, .little);
    return out;
}

/// Uniformly random element.
pub fn random(rand: std.Random) Gf2_128 {
    var b: [encoded_len]u8 = undefined;
    rand.bytes(&b);
    return fromBytes(b) catch unreachable;
}

/// Uniformly random element of the GF(2^16) subfield.
pub fn randomSubfield(rand: std.Random) Gf2_128 {
    var b: [subfield_encoded_len]u8 = undefined;
    rand.bytes(&b);
    return fromSubfieldBytes(b) catch unreachable;
}

/// Scratch length `extend` requires for a basis of `flen` evaluations:
/// the inverse table over the padded span, its batch-inversion prefix
/// products, and the evaluation points.
pub fn extendScratchLen(flen: usize) usize {
    const span = std.math.ceilPowerOfTwo(usize, flen) catch unreachable;
    return 2 * span - 1 + flen;
}

/// The `extend` operation from the specification: interprets `f` as the
/// evaluations of a polynomial of degree < `f.len` at the points inj(0),
/// inj(1), ..., and writes its evaluations at inj(0), ..., inj(out.len-1)
/// to `out`.
///
/// Uses Newton divided differences, built in place in `out`'s prefix, so
/// `f` must not alias `out`.
/// All point differences have the form inj(i) - inj(j) = inj(i xor j), so a
/// single batch inversion covers every denominator.
///
/// Asserts that `f` is not empty, that both sizes fit the inj domain, and
/// that `scratch` holds at least extendScratchLen(f.len) elements.
pub fn extend(out: []Gf2_128, f: []const Gf2_128, scratch: []Gf2_128) void {
    assert(f.len > 0 and f.len <= 1 << 16 and out.len <= 1 << 16);
    const n = out.len;
    @memcpy(out[0..@min(f.len, n)], f[0..@min(f.len, n)]);
    if (n <= f.len) return;

    const k = f.len;
    const span = std.math.ceilPowerOfTwo(usize, k) catch unreachable;
    assert(scratch.len >= extendScratchLen(k));

    // inv[d] = inj(d)^-1 for 1 <= d < span, covering every denominator
    // i xor (i - s) that the divided-difference table needs.
    const inv = scratch[0..span];
    for (inv[1..], 1..) |*e, d| e.* = inj(@intCast(d));
    batchInvert(inv[1..], scratch[span..][0 .. span - 1]);

    const xs = scratch[2 * span - 1 ..][0..k];
    for (xs, 0..) |*e, i| e.* = inj(@intCast(i));

    const dd = out[0..k];
    for (1..k) |s| {
        var i = k - 1;
        while (i >= s) : (i -= 1) {
            dd[i] = dd[i].add(dd[i - 1]).mul(inv[i ^ (i - s)]);
        }
    }

    for (k..n) |j| {
        const t = inj(@intCast(j));
        var acc = dd[k - 1];
        var i = k - 1;
        while (i > 0) {
            i -= 1;
            acc = acc.mul(.{ .v = t.v ^ xs[i].v }).add(dd[i]);
        }
        out[j] = acc;
    }
    // The prefix served as the coefficient table; the evaluations there
    // are just f itself.
    @memcpy(out[0..k], f);
}

/// Inverts every element of `vals` in place using Montgomery's batch trick.
/// All elements must be nonzero; `scratch` holds the prefix products.
fn batchInvert(vals: []Gf2_128, scratch: []Gf2_128) void {
    if (vals.len == 0) return;
    const prefix = scratch[0..vals.len];
    prefix[0] = vals[0];
    for (1..vals.len) |i| prefix[i] = prefix[i - 1].mul(vals[i]);

    var acc = prefix[vals.len - 1].invert().?;
    var i = vals.len;
    while (i > 1) {
        i -= 1;
        const inv_i = acc.mul(prefix[i - 1]);
        acc = acc.mul(vals[i]);
        vals[i] = inv_i;
    }
    vals[0] = acc;
}

fn mulSlow(a: Gf2_128, b: Gf2_128) Gf2_128 {
    var r: u128 = 0;
    var aa = a.v;
    var bb = b.v;
    for (0..128) |_| {
        if (bb & 1 != 0) r ^= aa;
        bb >>= 1;
        const carry = aa >> 127;
        aa <<= 1;
        if (carry != 0) aa ^= 0x87;
    }
    return .{ .v = r };
}

test "multiplication against a bitwise reference" {
    const samples = [_]u128{
        1,
        2,
        0x87,
        0x123456789abcdef0fedcba9876543210,
        std.math.maxInt(u128),
        1 << 127,
        0x243f6a8885a308d313198a2e03707344,
        0xa4093822299f31d0082efa98ec4e6c89,
    };
    for (samples) |a| {
        for (samples) |b| {
            const x: Gf2_128 = .{ .v = a };
            const y: Gf2_128 = .{ .v = b };
            try std.testing.expectEqual(mulSlow(x, y).v, x.mul(y).v);
            try std.testing.expectEqual(mulSlow(x, x).v, x.square().v);
        }
    }
}

test "known answers from an independent implementation" {
    try std.testing.expectEqual(0x5c5971877501d4b8f1871e01b64fda4c, g.v);
    try std.testing.expectEqual(0x8bb99658eaf2cae0a6e310fb6e176ea8, beta[2].v);
    try std.testing.expectEqual(0xb61e08da12f9665c3f8de8a2f9ff7eed, beta[3].v);

    const a: Gf2_128 = .{ .v = 0x0123456789abcdef0123456789abcdef };
    const b: Gf2_128 = .{ .v = 0xfedcba9876543210fedcba9876543210 };
    try std.testing.expectEqual(0x725cfee53719bb81d3fd5f4496b81a20, a.mul(b).v);
    try std.testing.expectEqual(0xeb702ab8a8e5b420519165b8928df41f, a.invert().?.v);
}

test "field axioms and inversion" {
    const a: Gf2_128 = .{ .v = 0x0123456789abcdef0123456789abcdef };
    const b: Gf2_128 = .{ .v = 0xfedcba9876543210fedcba9876543210 };
    const c: Gf2_128 = .{ .v = 0xdeadbeef };
    try std.testing.expect(a.mul(b).eql(b.mul(a)));
    try std.testing.expect(a.mul(b.add(c)).eql(a.mul(b).add(a.mul(c))));
    try std.testing.expect(a.mul(one).eql(a));
    try std.testing.expect(a.invert().?.mul(a).eql(one));
    try std.testing.expect(zero.invert() == null);
}

test "x generates the multiplicative group" {
    const x: Gf2_128 = .{ .v = 2 };
    const order = std.math.maxInt(u128);
    try std.testing.expect(x.pow(order).eql(one));
    // 2^128 - 1 = 3 * 5 * 17 * 257 * 641 * 65537 * 274177 * 6700417 * 67280421310721
    const prime_factors = [_]u128{ 3, 5, 17, 257, 641, 65537, 274177, 6700417, 67280421310721 };
    for (prime_factors) |q| {
        try std.testing.expect(!x.pow(order / q).eql(one));
    }
}

test "subfield basis and coordinates" {
    // g generates the order-65535 subgroup.
    try std.testing.expect(g.pow(65535).eql(one));
    try std.testing.expect(!g.pow(65535 / 3).eql(one));
    try std.testing.expect(!g.pow(65535 / 5).eql(one));
    try std.testing.expect(!g.pow(65535 / 17).eql(one));
    try std.testing.expect(!g.pow(65535 / 257).eql(one));

    try std.testing.expect(inj(0).isZero());
    try std.testing.expect(inj(1).eql(one));
    try std.testing.expect(inj(2).eql(g));
    try std.testing.expect(p2.eql(g));

    const js = [_]u16{ 0, 1, 2, 3, 42, 255, 256, 4711, 65535 };
    for (js) |j| {
        try std.testing.expectEqual(j, inj(j).toSubfield().?);
    }

    // Subfield closure under multiplication.
    const s = inj(4711).mul(inj(42));
    try std.testing.expect(s.isInSubfield());

    // x has full order, so it cannot lie in the subfield.
    try std.testing.expect(!isInSubfield(.{ .v = 2 }));
}

test "serialization round trip" {
    const a: Gf2_128 = .{ .v = 0x0102030405060708090a0b0c0d0e0f10 };
    const bytes = a.toBytes();
    try std.testing.expectEqual(0x10, bytes[0]);
    try std.testing.expect((try fromBytes(bytes)).eql(a));
}

test "extend agrees with direct evaluation" {
    // P(t) = a t^2 + b t + c for fixed field constants.
    const a: Gf2_128 = .{ .v = 0x243f6a8885a308d313198a2e03707344 };
    const b: Gf2_128 = .{ .v = 0x452821e638d01377be5466cf34e90c6c };
    const c: Gf2_128 = .{ .v = 0xc0ac29b7c97c50dd3f84d5b5b5470917 };

    var f: [4]Gf2_128 = undefined;
    for (&f, 0..) |*e, i| {
        const t = inj(@intCast(i));
        e.* = a.mul(t).add(b).mul(t).add(c);
    }
    var ext: [12]Gf2_128 = undefined;
    var scratch: [extendScratchLen(f.len)]Gf2_128 = undefined;
    extend(&ext, &f, &scratch);
    for (ext, 0..) |e, i| {
        const t = inj(@intCast(i));
        try std.testing.expect(e.eql(a.mul(t).add(b).mul(t).add(c)));
    }
}

test "extend keeps subfield rows in the subfield" {
    var f: [5]Gf2_128 = undefined;
    for (&f, 0..) |*e, i| e.* = inj(@intCast(1000 + 37 * i));
    var ext: [20]Gf2_128 = undefined;
    var scratch: [extendScratchLen(f.len)]Gf2_128 = undefined;
    extend(&ext, &f, &scratch);
    for (ext) |e| try std.testing.expect(e.isInSubfield());
}

test "batch inversion" {
    var vals: [7]Gf2_128 = undefined;
    for (&vals, 0..) |*e, i| e.* = inj(@intCast(3 * i + 1));
    var inverted = vals;
    var scratch: [vals.len]Gf2_128 = undefined;
    batchInvert(&inverted, &scratch);
    for (vals, inverted) |v, iv| {
        try std.testing.expect(v.mul(iv).eql(one));
    }
}
