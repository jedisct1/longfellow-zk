//! Fiat-Shamir transcript.
//!
//! The transcript accumulates the prover's messages into a running SHA-256
//! hash.
//! Whenever a challenge is requested after a write, the digest of
//! everything written so far seeds a pseudo-random function (FSPRF) whose
//! stream is AES-256-ECB applied to a little-endian 128-bit block counter.
//! Challenges are drawn from that stream by rejection sampling.
//! Repeated draws without an intervening write continue the same stream.

const std = @import("std");
const aes = std.crypto.core.aes;
const Sha256 = std.crypto.hash.sha2.Sha256;
const assert = std.debug.assert;

sha: Sha256,
fs: ?Fsprf,

const Transcript = @This();

pub fn init(session_id: []const u8) Transcript {
    var t: Transcript = .{ .sha = Sha256.init(.{}), .fs = null };
    t.writeBytes(session_id);
    return t;
}

/// Appends a byte string: designator 0x00, 8-byte little-endian length,
/// then the bytes.
pub fn writeBytes(t: *Transcript, b: []const u8) void {
    t.append(&.{0x00});
    t.appendInt(u64, b.len);
    t.append(b);
}

/// Appends `n` zero bytes as a byte-string message, without materializing
/// them.
/// Used for the correlation-intractability padding.
pub fn writeZeros(t: *Transcript, n: usize) void {
    t.append(&.{0x00});
    t.appendInt(u64, n);
    const chunk: [64]u8 = @splat(0);
    var left = n;
    while (left > 0) {
        const take = @min(left, chunk.len);
        t.append(chunk[0..take]);
        left -= take;
    }
}

/// Appends one field element: designator 0x01, then its canonical
/// little-endian serialization.
pub fn writeField(t: *Transcript, comptime F: type, e: F) void {
    t.append(&.{0x01});
    t.append(&e.toBytes());
}

/// Appends an array of field elements: designator 0x02, 8-byte
/// little-endian element count, then the serialized elements in order.
pub fn writeFieldArray(t: *Transcript, comptime F: type, elems: []const F) void {
    t.append(&.{0x02});
    t.appendInt(u64, elems.len);
    for (elems) |e| t.append(&e.toBytes());
}

/// Generates a natural number in [0, m) by rejection sampling, reading
/// ceil(bitlen(m) / 8) stream bytes per attempt.
pub fn generateNat(t: *Transcript, m: u64) u64 {
    assert(m >= 1);
    const l: u7 = 64 - @clz(m);
    const nbytes: usize = (l + 7) / 8;
    const mask = if (l == 64) std.math.maxInt(u64) else (@as(u64, 1) << @intCast(l)) - 1;
    const fs = t.prf();
    while (true) {
        var b: [8]u8 = @splat(0);
        fs.bytes(b[0..nbytes]);
        const r = std.mem.readInt(u64, &b, .little) & mask;
        if (r < m) return r;
    }
}

/// Fills `dst` with distinct naturals in [0, m), in the order produced by
/// the partial Fisher-Yates shuffle from the specification.
///
/// The shuffled array is never materialized.
/// The raw draws are recorded first; each output is then the value the
/// drawn slot held at that point, found by chasing the earlier swaps that
/// displaced it.
/// Resolving in reverse keeps the raw draws below the current index
/// intact for the chase.
pub fn generateNatsWithoutReplacement(t: *Transcript, dst: []usize, m: usize) void {
    assert(m > dst.len);
    for (dst, 0..) |*e, i| {
        e.* = i + t.generateNat(m - i);
    }
    var i = dst.len;
    while (i > 0) {
        i -= 1;
        // Position p was last touched by the latest earlier draw of p,
        // which moved the value that slot's source held at that time;
        // follow the trail until an undisturbed slot is reached.
        var p = dst[i];
        var limit = i;
        chase: while (true) {
            var k = limit;
            while (k > 0) {
                k -= 1;
                if (dst[k] == p) {
                    p = k;
                    limit = k;
                    continue :chase;
                }
            }
            break;
        }
        dst[i] = p;
    }
}

/// Generates one field element by rejection sampling on the canonical
/// byte encoding.
pub fn generateField(t: *Transcript, comptime F: type) F {
    const fs = t.prf();
    while (true) {
        var b: [F.encoded_len]u8 = undefined;
        fs.bytes(&b);
        return F.fromBytes(b) catch continue;
    }
}

/// Fills `dst` with field elements, in ascending index order.
pub fn generateChallenge(t: *Transcript, comptime F: type, dst: []F) void {
    for (dst) |*e| e.* = t.generateField(F);
}

fn append(t: *Transcript, data: []const u8) void {
    t.sha.update(data);
    t.fs = null;
}

fn appendInt(t: *Transcript, comptime T: type, x: T) void {
    var b: [@divExact(@bitSizeOf(T), 8)]u8 = undefined;
    std.mem.writeInt(T, &b, x, .little);
    t.append(&b);
}

fn prf(t: *Transcript) *Fsprf {
    if (t.fs == null) t.fs = Fsprf.init(t.sha.peek());
    return &t.fs.?;
}

/// The Fiat-Shamir pseudo-random function: an infinite byte stream where
/// block i is AES-256-ECB(seed, LE128(i)).
const Fsprf = struct {
    ctx: aes.AesEncryptCtx(aes.Aes256),
    counter: u128,
    buf: [16]u8,
    avail: usize,

    fn init(seed: [32]u8) Fsprf {
        return .{
            .ctx = aes.Aes256.initEnc(seed),
            .counter = 0,
            .buf = undefined,
            .avail = 0,
        };
    }

    fn bytes(f: *Fsprf, out: []u8) void {
        var i: usize = 0;
        while (i < out.len) {
            if (f.avail == 0) {
                var id: [16]u8 = undefined;
                std.mem.writeInt(u128, &id, f.counter, .little);
                f.ctx.encrypt(&f.buf, &id);
                f.counter += 1;
                f.avail = 16;
            }
            const take = @min(f.avail, out.len - i);
            @memcpy(out[i..][0..take], f.buf[16 - f.avail ..][0..take]);
            f.avail -= take;
            i += take;
        }
    }
};

const Secp256k1 = @import("field.zig").Secp256k1;

test "specification test vectors" {
    var t = Transcript.init("test");

    // Vector 1: write bytes 0..99, then generate 16 field elements.
    var data: [100]u8 = undefined;
    for (&data, 0..) |*b, i| b.* = @intCast(i);
    t.writeBytes(&data);

    const v1 = [16]u256{
        0x8b297f0bffd583c6c6b6796385d5fd20a08665733b833970ebdd1054bbbc1b14,
        0x0667c08ad7f38efec5f30dc8aa4f20d749cdcf96d63a770f9810ac5c0ca8dcb1,
        0xc8037fc12d4da00b5dc7597e3042f33f72a06f970cb71fb6b103ebb5419d8a6b,
        0xfbbcfa1eac48728fbfdacc1c21e2f78119457e0846337e46140e38e62856c4c5,
        0x5358ae603691cc759faeb572fb6642654ea1c3dbc8f81d00276dd8c4df95aa58,
        0x5266158c3c895dede5a23b6ce85a9f564b8059ebfcd1741f54497ec58189873e,
        0x3ecea4b2343c007fc32f2aff40dc7320945f101ecae5d52494db21ad326e9739,
        0x6462dd575e6b874118607212feec7ce5417ae3bf0f2e86604596f35d48bbaea2,
        0x6d56c703c369edea3595db6b958241580ae9b4a76fead961413ed9e9e5852dcd,
        0x6d31073cee650212a71b7b13e9f951e00ef3b14a008a79dd95047b26a4a83d06,
        0x1b9e2a6666da63c43e52227d91a8a7f0bd5311f63c2e3a18839133375639e6cb,
        0x332ea49dd23dd4745631ecbb15696192b1fa127256baf7a0483fd27db6f09a48,
        0x43e735927ccbdc4d5ce912675d638d6d3dc8eef3def34504304e938846f157d6,
        0xdc4a8868ae75e733a7257a8589230392a98d78594836dfccd01304742b5b3ad5,
        0x976353931711c634f2691e507b119fd7f6e653d419a2620676122db08db18765,
        0x332729ab436dca654866a9382deaee0add6fb7e90a80261f1488e56598e8bc99,
    };
    for (v1) |want| {
        try std.testing.expectEqual(want, t.generateField(Secp256k1).toInt());
    }

    // Vector 2: write the field element 7, then generate 16 elements.
    t.writeField(Secp256k1, Secp256k1.fromInt(7));
    const v2 = [16]u256{
        0x609db3e9a8f548df038519fa46cef23eb8c6553d3c1f698604e60a51613a738e,
        0x1cb69cb31999eb88e83c7586aac53f5e3286b084b0cf9e43619b48df01e0a310,
        0x3bf36e3ddc690a1b12b417628c115959b373d056c90c42dc2417baf46f538868,
        0xe336594f29dcda52e48896517b5cdb2d062ffd861ab02db5f8ca197aacc635f6,
        0xc1f396a8bad16bb0f57da6d380402a25b571bd4691226d11449a741440e325c8,
        0x5195336ec73751de066e3a8939b40c3c5555f1a513486dfc50dcf4c2d47e6ff2,
        0x8dcf872f3ded2b7ed1d1ee9a2b125bedc6eacd3c09b3a4a5286d8fc2fc3a6634,
        0x950dd2ef7be25eab686a6688497962ee4ad521da12b9ff3d8e56ad9435885b12,
        0xe14389d1d8448678cac33fdbc9aab20dba019e75149d170dd2f353891cd4b84f,
        0xe84906c09cd6423865baf64e48027cc598d52bdb90b17524c87ea892e53b5200,
        0x493cea587f1ec5622c04221cd6e5a41c26c1c1c24c0375f7aaa367d9678d83bc,
        0x5aca0010aced30bcb3b84a7f10ea39c4269ab7c92fcb6cff52958d8921ef2cc5,
        0x4498fa8340f41467c0fa813bd0ca83ef6e1c4b85c7b1168a94339fd9e8296139,
        0xf9a95b738a8e775421b1baa503abbeed2d283b236ebba25e1954b3c993d30a3d,
        0x98178711d03a0b1204ebb56b37bd3a2724dfb08e4dc925609391768b126d21f2,
        0x79251f49534f5c4b10b798b2dbf6e80a3b07593f616ce6a9617ccc61040aac78,
    };
    for (v2) |want| {
        try std.testing.expectEqual(want, t.generateField(Secp256k1).toInt());
    }

    // Vector 3: write the field element array [8, 9], then generate 16
    // elements.
    t.writeFieldArray(Secp256k1, &.{ Secp256k1.fromInt(8), Secp256k1.fromInt(9) });
    const v3 = [16]u256{
        0xae1a921288590205fc24543303ff527476359b8db4a983b2886a133b02f3217e,
        0x8c5d52a04b295f9fdb45ab66100fa00ca32c9634aa87cbbdb2bc3e1912459feb,
        0x12f82963b5b242156f6e9eb756eddee7652b60c7d6394403f7bd995e0b9bcd9c,
        0x880aa50b049b3939055deb7933749d338bb3fb5f64a9adf95019e6cfc232995c,
        0xf8558f693f0fa6df20a37147a898fb4c678831f566d80113bbe2cdcd18285da2,
        0xbbcc8d9b46f88bc8c6cec0ad2d5e49508b7db91d548548eddc61800de1329e1c,
        0x479a17244398caae8155a73438a22583df7de10a8a2e12ad53ddd3bc7305fac9,
        0x9ba1917f1227932250288a843f64b4e7b7f47a5fbc16c111f6e1f76235ccf38c,
        0xd1582138045d1636fb7f677c9e8a4a4143ce2b2bb54fb4f49fb0ad1fee5df6b4,
        0x05331e5b8508f79c017a8dfbbb805f3f8c5e3e4bc417e44849b9212439646331,
        0xb6b95862194ca52dcaa9ee651b7fc5b708f43feae108bb9a7f95213f4d069048,
        0xe86b1602f0a54c4e237867ebaf05e7581464fd238e50f6ed9c3cea63909c8e60,
        0xb7280439f3b21b113ff29cefe39292d5e2d137709c3d3cec36473a0f97a24e62,
        0xbeaa5e08257d232506fb3e46c6daa29e0859c34c7d0cd673bc6706ee261ae059,
        0x0691ead55728cd087a1952b22b6628ba4e26fbefc8debeec5e6fbc3a16f637be,
        0x47dc31f6d8bc9c44290781176df3e4b95ac8793a4a42fa5859c564d92d6d5af5,
    };
    for (v3) |want| {
        try std.testing.expectEqual(want, t.generateField(Secp256k1).toInt());
    }

    // Vector 4: write the string "nats", then a list of generate_nat calls.
    t.writeBytes("nats");
    const nat_params = [_]u64{ 1, 1, 1, 2, 2, 2, 7, 7, 7, 7, 32, 32, 32, 32, 256, 256, 256, 256, 1000, 10000, 60000, 65535, 100000, 100000 };
    const nat_want = [_]u64{ 0, 0, 0, 0, 0, 0, 3, 0, 4, 5, 10, 30, 27, 22, 100, 189, 3, 92, 999, 3105, 40886, 51590, 56367, 10678 };
    for (nat_params, nat_want) |m, want| {
        try std.testing.expectEqual(want, t.generateNat(m));
    }

    // Vector 5: write a 6-byte string, then sample without replacement.
    // The prose in testvectors.md says the string is "choice", but the
    // published lists require "choose" (see SPEC_ISSUES.md).
    t.writeBytes("choose");
    const choice_want = [_][20]usize{
        .{ 10, 29, 30, 11, 4, 15, 16, 28, 19, 21, 25, 18, 17, 3, 5, 23, 24, 22, 6, 1 },
        .{ 3, 17, 18, 8, 30, 7, 14, 19, 25, 23, 12, 4, 31, 16, 0, 6, 20, 27, 11, 10 },
        .{ 9, 56, 61, 45, 35, 53, 51, 3, 39, 32, 31, 6, 59, 58, 54, 22, 27, 62, 55, 19 },
        .{ 12, 52, 39, 17, 51, 38, 58, 2, 28, 27, 46, 63, 61, 50, 40, 55, 47, 13, 56, 32 },
        .{ 157, 668, 572, 138, 913, 994, 797, 249, 440, 723, 489, 241, 383, 108, 710, 341, 406, 585, 42, 692 },
        .{ 40745, 48408, 17108, 44500, 53993, 10008, 24910, 52200, 61265, 54989, 41237, 25958, 28697, 61187, 34729, 3525, 9005, 38627, 9724, 12169 },
    };
    const choice_m = [_]usize{ 31, 32, 63, 64, 1000, 65535 };
    for (choice_m, choice_want) |m, want| {
        var got: [20]usize = undefined;
        t.generateNatsWithoutReplacement(&got, m);
        try std.testing.expectEqualSlices(usize, &want, &got);
    }
}

test "stream continuity and reseeding" {
    var t = Transcript.init("abc");
    const a = t.generateNat(1 << 62);
    const b = t.generateNat(1 << 62);
    // Drawing twice continues the stream rather than restarting it.
    try std.testing.expect(a != b);

    // A write reseeds deterministically: two transcripts with the same
    // history agree.
    var t2 = Transcript.init("abc");
    _ = t2.generateNat(1 << 62);
    _ = t2.generateNat(1 << 62);
    t.writeBytes("x");
    t2.writeBytes("x");
    try std.testing.expectEqual(t.generateNat(1000), t2.generateNat(1000));
}
