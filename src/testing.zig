//! Shared test fixtures.
//!
//! The s-gonal circuit from the specification test vectors: C(n, m, s) = 0
//! iff n is the m-th s-gonal number, over Fp128, with inputs (1, n, m, s).
//! The published vector predates the current wire format, so
//! `sgonal_vector_bytes` splices in the missing subfield_boundary field
//! and appends a placeholder id (see SPEC_ISSUES.md 16b).

const std = @import("std");
const Allocator = std.mem.Allocator;

const circuit = @import("circuit.zig");
const Fp128 = @import("field.zig").Fp128;

/// The vector exactly as published in the draft (stale format).
pub const sgonal_stale_hex =
    "01060000010000010000020000040000020000040000" ++
    "ffffffffffffffffffffffffffefffff" ++
    "00000000000000000000000000f0ffff" ++
    "01000000000000000000000000000000" ++
    "fdffffffffffffffffffffffffefffff" ++
    "030000060000030000000000020000000000000000000000080000040000010000" ++
    "000000030000020000020000020000040000080000000000000000000000020000" ++
    "060000000000000000000000040000000000000000030000090000020000000000" ++
    "020000020000020000000000020000020000020000000000020000040000000000" ++
    "000000020000030000030000040000020000";

/// 45 is the 5th hexagonal number: 2*45 = (6-2)*25 - (6-4)*5.
pub const sgonal_inputs = [4]Fp128{ .fromInt(1), .fromInt(45), .fromInt(5), .fromInt(6) };

/// The vector adapted to the current format: subfield_boundary = 0
/// spliced in after npub_in, and an all-zero id appended.
pub const sgonal_vector_bytes = blk: {
    @setEvalBranchQuota(10_000);
    var stale: [sgonal_stale_hex.len / 2]u8 = undefined;
    _ = std.fmt.hexToBytes(&stale, sgonal_stale_hex) catch unreachable;

    // Header prefix through npub_in: version (1) + field id (3) + nv (3)
    // + nc (3) + npub_in (3).
    const boundary_at = 1 + 4 * circuit.size_len;
    break :blk stale[0..boundary_at].* ++ [_]u8{ 0, 0, 0 } ++
        stale[boundary_at..].* ++ @as([circuit.id_len]u8, @splat(0));
};

/// The deserialized circuit with its id recomputed.
pub fn sgonalCircuit(gpa: Allocator) !circuit.Circuit(Fp128) {
    var c = try circuit.Circuit(Fp128).fromBytes(gpa, &sgonal_vector_bytes, false);
    c.id = c.computeId();
    return c;
}
