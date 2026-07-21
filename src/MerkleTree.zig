//! Merkle tree over SHA-256 with batched inclusion proofs.
//!
//! The tree is stored as a flat array of 2n digests in heap order: leaves
//! occupy indices n..2n, and node i is the hash of the concatenation of
//! nodes 2i and 2i+1.
//! The root is node 1.
//! The leaf count n need not be a power of two.
//! Batch proofs contain exactly the sibling digests that the verifier
//! cannot derive from the leaves it already knows, in the fixed top-down
//! node order both sides share.

const std = @import("std");
const Sha256 = std.crypto.hash.sha2.Sha256;
const Allocator = std.mem.Allocator;
const assert = std.debug.assert;

n: usize,
nodes: []Digest,

const MerkleTree = @This();

pub const Digest = [Sha256.digest_length]u8;

pub fn init(gpa: Allocator, n: usize) Allocator.Error!MerkleTree {
    assert(n > 0);
    const nodes = try gpa.alloc(Digest, 2 * n);
    return .{ .n = n, .nodes = nodes };
}

pub fn deinit(m: *MerkleTree, gpa: Allocator) void {
    gpa.free(m.nodes);
    m.* = undefined;
}

pub fn setLeaf(m: *MerkleTree, pos: usize, leaf: Digest) void {
    assert(pos < m.n);
    m.nodes[pos + m.n] = leaf;
}

/// Computes all internal nodes and returns the root.
/// Every leaf must have been set.
pub fn build(m: *MerkleTree) Digest {
    var i = m.n - 1;
    while (i >= 1) : (i -= 1) {
        m.nodes[i] = hashPair(m.nodes[2 * i], m.nodes[2 * i + 1]);
    }
    return m.nodes[1];
}

/// Produces a batch inclusion proof for the leaves at `requested`, which
/// must contain no duplicates.
pub fn compressedProof(m: MerkleTree, gpa: Allocator, requested: []const usize) Allocator.Error![]Digest {
    const marked = try gpa.alloc(bool, 2 * m.n);
    defer gpa.free(marked);
    markTree(marked, m.n, requested);

    var count: usize = 0;
    var i = m.n - 1;
    while (i >= 1) : (i -= 1) {
        if (marked[i] and unresolvedChild(marked, i) != null) count += 1;
    }

    const proof = try gpa.alloc(Digest, count);
    var k: usize = 0;
    i = m.n - 1;
    while (i >= 1) : (i -= 1) {
        if (marked[i]) {
            if (unresolvedChild(marked, i)) |child| {
                proof[k] = m.nodes[child];
                k += 1;
            }
        }
    }
    return proof;
}

/// Checks that `leaves[i]` sits at position `indices[i]` of the `n`-leaf
/// tree with the given root.
/// Duplicate indices, unconsumed proof digests, and the empty claim are
/// all rejected.
pub fn verify(
    gpa: Allocator,
    root: Digest,
    n: usize,
    leaves: []const Digest,
    indices: []const usize,
    proof: []const Digest,
) Allocator.Error!bool {
    if (leaves.len == 0 or leaves.len != indices.len) return false;
    for (indices) |i| {
        if (i >= n) return false;
    }

    const flags = try gpa.alloc(bool, 4 * n);
    defer gpa.free(flags);
    const marked = flags[0 .. 2 * n];
    markTree(marked, n, indices);
    const defined = flags[2 * n ..];
    @memset(defined, false);
    const nodes = try gpa.alloc(Digest, 2 * n);
    defer gpa.free(nodes);

    var proof_index: usize = 0;
    var i = n - 1;
    while (i >= 1) : (i -= 1) {
        if (marked[i]) {
            if (unresolvedChild(marked, i)) |child| {
                if (proof_index >= proof.len) return false;
                nodes[child] = proof[proof_index];
                proof_index += 1;
                defined[child] = true;
            }
        }
    }

    for (leaves, indices) |leaf, pos| {
        if (defined[pos + n]) return false;
        nodes[pos + n] = leaf;
        defined[pos + n] = true;
    }

    i = n - 1;
    while (i >= 1) : (i -= 1) {
        if (defined[2 * i] and defined[2 * i + 1]) {
            nodes[i] = hashPair(nodes[2 * i], nodes[2 * i + 1]);
            defined[i] = true;
        }
    }

    return proof_index == proof.len and defined[1] and std.mem.eql(u8, &nodes[1], &root);
}

/// The child of node `i` whose digest a proof must supply, or null if
/// both children are already covered by requested leaves.
/// Prover and verifier must agree on this choice, so it lives in one
/// place.
fn unresolvedChild(marked: []const bool, i: usize) ?usize {
    var child = 2 * i;
    if (marked[child]) child += 1;
    return if (marked[child]) null else child;
}

/// Upper bound on the number of digests in a proof for a single leaf of
/// an n-leaf tree.
pub fn maxProofLen(n: usize) usize {
    return std.math.log2_int(usize, 2 * n - 1) + 1;
}

fn markTree(marked: []bool, n: usize, requested: []const usize) void {
    assert(marked.len == 2 * n);
    @memset(marked, false);
    for (requested) |i| {
        assert(i < n);
        marked[i + n] = true;
    }
    var i = n - 1;
    while (i >= 1) : (i -= 1) {
        marked[i] = marked[2 * i] or marked[2 * i + 1];
    }
}

fn hashPair(left: Digest, right: Digest) Digest {
    var h = Sha256.init(.{});
    h.update(&left);
    h.update(&right);
    var out: Digest = undefined;
    h.final(&out);
    return out;
}

fn leafFromHex(hex: *const [64]u8) Digest {
    var out: Digest = undefined;
    _ = std.fmt.hexToBytes(&out, hex) catch unreachable;
    return out;
}

const test_leaves = [5]*const [64]u8{
    "4bf5122f344554c53bde2ebb8cd2b7e3d1600ad631c385a5d7cce23c7785459a",
    "dbc1b4c900ffe48d575b5da5c638040125f65db0fe3e24494b76ea986457d986",
    "084fed08b978af4d7d196a7446a86b58009e636b611db16211b65a9aadff29c5",
    "e52d9c508c502347344d8c07ad91cbd6068afc75ff6292f062a09ca381c89e71",
    "e77b9a9ae9e30b0dbdb6f510a264ef9de781501d7b6b92ae89eb059c5ab743db",
};

test "specification test vector" {
    const gpa = std.testing.allocator;

    var m = try MerkleTree.init(gpa, test_leaves.len);
    defer m.deinit(gpa);
    for (test_leaves, 0..) |hex, i| m.setLeaf(i, leafFromHex(hex));
    const root = m.build();

    try std.testing.expectEqualStrings(
        "f22f4501ffd3bdffcecc9e4cd6828a4479aeedd6aa484eb7c1f808ccf71c6e76",
        &std.fmt.bytesToHex(root, .lower),
    );

    const proof01 = try m.compressedProof(gpa, &.{ 0, 1 });
    defer gpa.free(proof01);
    try std.testing.expectEqual(2, proof01.len);
    try std.testing.expectEqualStrings(
        "084fed08b978af4d7d196a7446a86b58009e636b611db16211b65a9aadff29c5",
        &std.fmt.bytesToHex(proof01[0], .lower),
    );
    try std.testing.expectEqualStrings(
        "f03808f5b8088c61286d505e8e93aa378991d9889ae2d874433ca06acabcd493",
        &std.fmt.bytesToHex(proof01[1], .lower),
    );

    const proof13 = try m.compressedProof(gpa, &.{ 1, 3 });
    defer gpa.free(proof13);
    try std.testing.expectEqual(3, proof13.len);
    try std.testing.expectEqualStrings(
        "e77b9a9ae9e30b0dbdb6f510a264ef9de781501d7b6b92ae89eb059c5ab743db",
        &std.fmt.bytesToHex(proof13[0], .lower),
    );
    try std.testing.expectEqualStrings(
        "084fed08b978af4d7d196a7446a86b58009e636b611db16211b65a9aadff29c5",
        &std.fmt.bytesToHex(proof13[1], .lower),
    );
    try std.testing.expectEqualStrings(
        "4bf5122f344554c53bde2ebb8cd2b7e3d1600ad631c385a5d7cce23c7785459a",
        &std.fmt.bytesToHex(proof13[2], .lower),
    );
}

test "verification accepts valid proofs and rejects tampering" {
    const gpa = std.testing.allocator;

    var m = try MerkleTree.init(gpa, test_leaves.len);
    defer m.deinit(gpa);
    for (test_leaves, 0..) |hex, i| m.setLeaf(i, leafFromHex(hex));
    const root = m.build();

    const cases = [_][]const usize{
        &.{ 0, 1 },
        &.{ 1, 3 },
        &.{ 4, 2, 0 },
        &.{ 0, 1, 2, 3, 4 },
        &.{2},
    };
    for (cases) |indices| {
        const proof = try m.compressedProof(gpa, indices);
        defer gpa.free(proof);
        var leaves: [5]Digest = undefined;
        for (indices, 0..) |leaf_index, k| leaves[k] = leafFromHex(test_leaves[leaf_index]);

        try std.testing.expect(try verify(gpa, root, 5, leaves[0..indices.len], indices, proof));

        var bad_root = root;
        bad_root[0] ^= 1;
        try std.testing.expect(!try verify(gpa, bad_root, 5, leaves[0..indices.len], indices, proof));

        var bad_leaves = leaves;
        bad_leaves[0][31] ^= 1;
        try std.testing.expect(!try verify(gpa, root, 5, bad_leaves[0..indices.len], indices, proof));

        if (proof.len > 0) {
            try std.testing.expect(!try verify(gpa, root, 5, leaves[0..indices.len], indices, proof[0 .. proof.len - 1]));
        }
    }

    // The empty claim fails by convention.
    try std.testing.expect(!try verify(gpa, root, 5, &.{}, &.{}, &.{}));
}

test "single leaf tree" {
    const gpa = std.testing.allocator;
    var m = try MerkleTree.init(gpa, 1);
    defer m.deinit(gpa);
    const leaf = leafFromHex(test_leaves[0]);
    m.setLeaf(0, leaf);
    const root = m.build();
    try std.testing.expectEqualSlices(u8, &leaf, &root);
    const proof = try m.compressedProof(gpa, &.{0});
    defer gpa.free(proof);
    try std.testing.expectEqual(0, proof.len);
    try std.testing.expect(try verify(gpa, root, 1, &.{leaf}, &.{0}, proof));
}
