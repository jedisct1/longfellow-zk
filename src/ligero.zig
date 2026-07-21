//! The Ligero commitment scheme and zero-knowledge argument for linear and
//! quadratic constraints over a committed witness vector.
//!
//! The prover lays the witness out in a tableau of NROW rows.
//! Each row holds NREQ blinding elements and W payload elements,
//! interpreted as evaluations of a polynomial of degree < BLOCK at the
//! field's canonical point sequence and extended to BLOCK_ENC evaluations
//! (a Reed-Solomon codeword).
//! The first three rows blind the low-degree, linear, and quadratic tests;
//! then come the witness rows; then triples of rows carrying copies
//! (x, y, x*y) for the quadratic constraints.
//! Columns DBLOCK.. are committed in a Merkle tree, each leaf hashing a
//! fresh random nonce followed by the column.
//! The verifier checks random linear combinations of the rows against a
//! random selection of opened columns.
//!
//! The row geometry and checks follow the reference implementation; the
//! draft's pseudocode is inconsistent on several points (see
//! SPEC_ISSUES.md items 4-13c).

const std = @import("std");
const Allocator = std.mem.Allocator;
const assert = std.debug.assert;
const Sha256 = std.crypto.hash.sha2.Sha256;

const Gf2_128 = @import("Gf2_128.zig");
const MerkleTree = @import("MerkleTree.zig");
const Transcript = @import("Transcript.zig");

pub const nonce_len = 32;
pub const Digest = MerkleTree.Digest;

pub const ParamError = error{InvalidParam};

pub const VerifyError = error{
    MerkleCheckFailed,
    LowDegreeCheckFailed,
    DotCheckFailed,
    WrongDotProduct,
    QuadraticCheckFailed,
} || Allocator.Error;

/// The quadratic constraint W[x] * W[y] = W[z].
pub const QuadraticConstraint = struct {
    x: usize,
    y: usize,
    z: usize,
};

pub fn Ligero(comptime F: type) type {
    return struct {
        /// A term of the sparse constraint matrix: A[c, w] += k, part of
        /// the linear system A * W = b.
        pub const LinearTerm = struct {
            c: usize,
            w: usize,
            k: F,
        };

        pub const Param = struct {
            nw: usize,
            nq: usize,
            /// Number of opened columns; also the number of blinding
            /// elements at the start of every row.
            nreq: usize,

            block_enc: usize,
            block: usize,
            dblock: usize,
            block_ext: usize,
            w: usize,
            nwrow: usize,
            nqtriples: usize,
            nwqrow: usize,
            nrow: usize,

            pub const ildt = 0;
            pub const idot = 1;
            pub const iquad = 2;
            pub const iw = 3;

            pub fn iq(p: Param) usize {
                return iw + p.nwrow;
            }

            pub fn init(nw: usize, nq: usize, rateinv: usize, nreq: usize, block_enc: usize) ParamError!Param {
                if (nreq == 0) return error.InvalidParam;
                if (block_enc + 1 < 2 + rateinv) return error.InvalidParam;
                const block = (block_enc + 1) / (2 + rateinv);
                if (block < nreq) return error.InvalidParam;
                const w = block - nreq;
                if (w < nreq or w == 0) return error.InvalidParam;
                const dblock = 2 * block - 1;
                if (block_enc < dblock) return error.InvalidParam;
                const block_ext = block_enc - dblock;
                if (block_ext <= nreq) return error.InvalidParam;
                // The evaluation points must be distinct, and for
                // GF(2^128) they must fit the inj domain.
                if (block_enc > F.extend_domain_limit) return error.InvalidParam;

                const nwrow = std.math.divCeil(usize, nw, w) catch unreachable;
                const nqtriples = std.math.divCeil(usize, nq, w) catch unreachable;
                const nwqrow = nwrow + 3 * nqtriples;
                return .{
                    .nw = nw,
                    .nq = nq,
                    .nreq = nreq,
                    .block_enc = block_enc,
                    .block = block,
                    .dblock = dblock,
                    .block_ext = block_ext,
                    .w = w,
                    .nwrow = nwrow,
                    .nqtriples = nqtriples,
                    .nwqrow = nwqrow,
                    .nrow = nwqrow + 3,
                };
            }
        };

        pub const Commitment = struct {
            root: Digest,
        };

        pub const Proof = struct {
            y_ldt: []F,
            y_dot: []F,
            y_quad_0: []F,
            y_quad_2: []F,
            /// Opened column entries, nrow * nreq, row-major.
            req: []F,
            nonces: [][nonce_len]u8,
            path: []Digest,

            pub fn deinit(p: *Proof, gpa: Allocator) void {
                gpa.free(p.y_ldt);
                gpa.free(p.y_dot);
                gpa.free(p.y_quad_0);
                gpa.free(p.y_quad_2);
                gpa.free(p.req);
                gpa.free(p.nonces);
                gpa.free(p.path);
                p.* = undefined;
            }
        };

        pub const Prover = struct {
            param: Param,
            tableau: []F,
            nonces: [][nonce_len]u8,
            /// Room for a row basis copy plus the field's extension
            /// scratch, so row extension never allocates.
            scratch: []F,
            tree: MerkleTree,

            pub fn init(gpa: Allocator, param: Param) Allocator.Error!Prover {
                const tableau = try gpa.alloc(F, param.nrow * param.block_enc);
                errdefer gpa.free(tableau);
                const nonces = try gpa.alloc([nonce_len]u8, param.block_ext);
                errdefer gpa.free(nonces);
                const scratch = try gpa.alloc(F, param.dblock + F.extendScratchLen(param.dblock));
                errdefer gpa.free(scratch);
                const tree = try MerkleTree.init(gpa, param.block_ext);
                return .{ .param = param, .tableau = tableau, .nonces = nonces, .scratch = scratch, .tree = tree };
            }

            pub fn deinit(p: *Prover, gpa: Allocator) void {
                gpa.free(p.tableau);
                gpa.free(p.nonces);
                gpa.free(p.scratch);
                p.tree.deinit(gpa);
                p.* = undefined;
            }

            fn row(p: *Prover, i: usize) []F {
                return p.tableau[i * p.param.block_enc ..][0..p.param.block_enc];
            }

            /// Reed-Solomon-extends the first `basis` entries of `dst`
            /// across the whole row, in place.
            fn extendRow(p: *Prover, dst: []F, basis: usize) void {
                const fcopy = p.scratch[0..basis];
                @memcpy(fcopy, dst[0..basis]);
                F.extend(dst, fcopy, p.scratch[basis..]);
            }

            /// Lays out the tableau for the witness and commits to it,
            /// writing the root to the transcript.
            /// Witnesses below `subfield_boundary` must lie in the
            /// subfield; a row whose payload sits entirely below the
            /// boundary gets subfield blinding, so the whole row stays
            /// subfield-valued.
            pub fn commit(
                p: *Prover,
                t: *Transcript,
                witness: []const F,
                subfield_boundary: usize,
                lqc: []const QuadraticConstraint,
                random: std.Random,
            ) Commitment {
                const par = p.param;
                assert(witness.len == par.nw);
                assert(lqc.len == par.nq);

                p.layoutBlindingRows(random);
                p.layoutWitnessRows(witness, subfield_boundary, random);
                p.layoutQuadraticRows(witness, lqc, random);

                for (0..par.block_ext) |j| {
                    random.bytes(&p.nonces[j]);
                    p.tree.setLeaf(j, leafHash(&p.nonces[j], p.tableau, par.dblock + j, par.block_enc, par.nrow));
                }
                const root = p.tree.build();
                t.writeBytes(&root);
                return .{ .root = root };
            }

            /// Produces a proof for the given constraints.
            /// The caller supplies the hash of the linear terms, which
            /// anchors the statement in the transcript.
            pub fn prove(
                p: *Prover,
                gpa: Allocator,
                t: *Transcript,
                nl: usize,
                llterm: []const LinearTerm,
                hash_of_llterm: Digest,
                lqc: []const QuadraticConstraint,
            ) Allocator.Error!Proof {
                const par = p.param;
                t.writeBytes(&hash_of_llterm);

                const scratch = try gpa.alloc(F, par.nwqrow + nl + 3 * par.nq +
                    par.nqtriples + par.nwqrow * par.w + par.block + 2 * par.dblock +
                    F.extendScratchLen(par.block));
                defer gpa.free(scratch);
                var rest = scratch;
                const u_ldt = take(&rest, par.nwqrow);
                const alphal = take(&rest, nl);
                const alphaq = take(&rest, 3 * par.nq);
                const u_quad = take(&rest, par.nqtriples);
                const a = take(&rest, par.nwqrow * par.w);
                const aext = take(&rest, par.block);
                const af = take(&rest, par.dblock);
                const y = take(&rest, par.dblock);

                // No transcript writes intervene, so drawing all four
                // challenge vectors up front reads the same stream as
                // drawing each at its point of use.
                t.generateChallenge(F, u_ldt);
                t.generateChallenge(F, alphal);
                t.generateChallenge(F, alphaq);
                t.generateChallenge(F, u_quad);

                const y_ldt = try gpa.alloc(F, par.block);
                errdefer gpa.free(y_ldt);
                @memcpy(y_ldt, p.row(Param.ildt)[0..par.block]);
                for (0..par.nwqrow) |i| {
                    addScaled(y_ldt, u_ldt[i], p.row(Param.iw + i)[0..par.block]);
                }

                innerProductVector(a, par, nl, llterm, alphal, lqc, alphaq);

                const y_dot = try gpa.alloc(F, par.dblock);
                errdefer gpa.free(y_dot);
                @memcpy(y_dot, p.row(Param.idot)[0..par.dblock]);
                for (0..par.nwqrow) |i| {
                    extendARow(af, par, a, i, aext, rest);
                    for (y_dot, af, p.row(Param.iw + i)[0..par.dblock]) |*yv, av, wv| {
                        yv.* = yv.add(av.mul(wv));
                    }
                }

                const y_quad_0 = try gpa.alloc(F, par.nreq);
                errdefer gpa.free(y_quad_0);
                const y_quad_2 = try gpa.alloc(F, par.dblock - par.block);
                errdefer gpa.free(y_quad_2);
                {
                    @memcpy(y, p.row(Param.iquad)[0..par.dblock]);
                    const iqx = par.iq();
                    const iqy = iqx + par.nqtriples;
                    const iqz = iqy + par.nqtriples;
                    for (0..par.nqtriples) |i| {
                        for (y, p.row(iqx + i)[0..par.dblock], p.row(iqy + i)[0..par.dblock], p.row(iqz + i)[0..par.dblock]) |*yv, xv, yv2, zv| {
                            yv.* = yv.add(u_quad[i].mul(zv.sub(xv.mul(yv2))));
                        }
                    }
                    for (y[par.nreq..][0..par.w]) |v| assert(v.isZero());
                    @memcpy(y_quad_0, y[0..par.nreq]);
                    @memcpy(y_quad_2, y[par.block..par.dblock]);
                }

                t.writeFieldArray(F, y_ldt);
                t.writeFieldArray(F, y_dot);
                t.writeFieldArray(F, y_quad_0);
                t.writeFieldArray(F, y_quad_2);

                const idx = try gpa.alloc(usize, par.nreq);
                defer gpa.free(idx);
                t.generateNatsWithoutReplacement(idx, par.block_ext);

                const req = try gpa.alloc(F, par.nrow * par.nreq);
                errdefer gpa.free(req);
                for (0..par.nrow) |i| {
                    for (idx, 0..) |col, k| {
                        req[i * par.nreq + k] = p.tableau[i * par.block_enc + par.dblock + col];
                    }
                }

                const nonces = try gpa.alloc([nonce_len]u8, par.nreq);
                errdefer gpa.free(nonces);
                for (idx, nonces) |col, *n| n.* = p.nonces[col];

                const path = try p.tree.compressedProof(gpa, idx);

                return .{
                    .y_ldt = y_ldt,
                    .y_dot = y_dot,
                    .y_quad_0 = y_quad_0,
                    .y_quad_2 = y_quad_2,
                    .req = req,
                    .nonces = nonces,
                    .path = path,
                };
            }

            fn layoutBlindingRows(p: *Prover, random: std.Random) void {
                const par = p.param;

                const ldt = p.row(Param.ildt);
                for (ldt[0..par.block]) |*e| e.* = F.random(random);
                p.extendRow(ldt, par.block);

                const dot = p.row(Param.idot);
                for (dot[0..par.dblock]) |*e| e.* = F.random(random);
                var sum = F.zero;
                for (dot[par.nreq..][0..par.w]) |e| sum = sum.add(e);
                dot[par.nreq] = dot[par.nreq].sub(sum);
                p.extendRow(dot, par.dblock);

                const quad = p.row(Param.iquad);
                for (quad[0..par.dblock]) |*e| e.* = F.random(random);
                @memset(quad[par.nreq..][0..par.w], F.zero);
                p.extendRow(quad, par.dblock);
            }

            fn layoutWitnessRows(
                p: *Prover,
                witness: []const F,
                subfield_boundary: usize,
                random: std.Random,
            ) void {
                const par = p.param;
                for (0..par.nwrow) |i| {
                    const dst = p.row(Param.iw + i);
                    const subfield_only = (i + 1) * par.w <= subfield_boundary;
                    for (dst[0..par.nreq]) |*e| {
                        e.* = if (subfield_only) F.randomSubfield(random) else F.random(random);
                    }
                    @memset(dst[par.nreq..][0..par.w], F.zero);
                    const n = @min(par.w, par.nw - i * par.w);
                    @memcpy(dst[par.nreq..][0..n], witness[i * par.w ..][0..n]);
                    p.extendRow(dst, par.block);
                }
            }

            fn layoutQuadraticRows(
                p: *Prover,
                witness: []const F,
                lqc: []const QuadraticConstraint,
                random: std.Random,
            ) void {
                const par = p.param;
                const iqx = par.iq();
                const iqy = iqx + par.nqtriples;
                const iqz = iqy + par.nqtriples;
                for (0..par.nqtriples) |i| {
                    const rows = [3][]F{ p.row(iqx + i), p.row(iqy + i), p.row(iqz + i) };
                    for (rows) |dst| {
                        for (dst[0..par.nreq]) |*e| e.* = F.random(random);
                        @memset(dst[par.nreq..][0..par.w], F.zero);
                    }
                    var j: usize = 0;
                    while (j < par.w and j + i * par.w < par.nq) : (j += 1) {
                        const l = lqc[j + i * par.w];
                        assert(witness[l.z].eql(witness[l.x].mul(witness[l.y])));
                        rows[0][par.nreq + j] = witness[l.x];
                        rows[1][par.nreq + j] = witness[l.y];
                        rows[2][par.nreq + j] = witness[l.z];
                    }
                    for (rows) |dst| p.extendRow(dst, par.block);
                }
            }
        };

        /// Verifies a proof against a commitment.
        /// The transcript must be in the same state as the prover's after
        /// `commit`.
        pub fn verify(
            gpa: Allocator,
            par: Param,
            commitment: Commitment,
            proof: Proof,
            t: *Transcript,
            llterm: []const LinearTerm,
            hash_of_llterm: Digest,
            b: []const F,
            lqc: []const QuadraticConstraint,
        ) VerifyError!void {
            if (proof.y_ldt.len != par.block or proof.y_dot.len != par.dblock or
                proof.y_quad_0.len != par.nreq or proof.y_quad_2.len != par.dblock - par.block or
                proof.req.len != par.nrow * par.nreq or proof.nonces.len != par.nreq)
            {
                return error.MerkleCheckFailed;
            }

            t.writeBytes(&hash_of_llterm);

            const scratch = try gpa.alloc(F, par.nwqrow + b.len + 3 * par.nq +
                par.nqtriples + par.nreq + par.nwqrow * par.w + par.block +
                2 * par.block_enc + par.dblock + F.extendScratchLen(par.dblock));
            defer gpa.free(scratch);
            var rest = scratch;
            const u_ldt = take(&rest, par.nwqrow);
            const alphal = take(&rest, b.len);
            const alphaq = take(&rest, 3 * par.nq);
            const u_quad = take(&rest, par.nqtriples);
            const yc = take(&rest, par.nreq);
            const a = take(&rest, par.nwqrow * par.w);
            const aext = take(&rest, par.block);
            const af = take(&rest, par.block_enc);
            const ext = take(&rest, par.block_enc);
            const yquad = take(&rest, par.dblock);

            t.generateChallenge(F, u_ldt);
            t.generateChallenge(F, alphal);
            t.generateChallenge(F, alphaq);
            t.generateChallenge(F, u_quad);

            t.writeFieldArray(F, proof.y_ldt);
            t.writeFieldArray(F, proof.y_dot);
            t.writeFieldArray(F, proof.y_quad_0);
            t.writeFieldArray(F, proof.y_quad_2);

            const idx = try gpa.alloc(usize, par.nreq);
            defer gpa.free(idx);
            t.generateNatsWithoutReplacement(idx, par.block_ext);

            {
                const leaves = try gpa.alloc(Digest, par.nreq);
                defer gpa.free(leaves);
                for (leaves, 0..) |*leaf, k| {
                    leaf.* = leafHash(&proof.nonces[k], proof.req, k, par.nreq, par.nrow);
                }
                const ok = try MerkleTree.verify(gpa, commitment.root, par.block_ext, leaves, idx, proof.path);
                if (!ok) return error.MerkleCheckFailed;
            }

            {
                @memcpy(yc, proof.req[Param.ildt * par.nreq ..][0..par.nreq]);
                for (0..par.nwqrow) |i| {
                    addScaled(yc, u_ldt[i], proof.req[(Param.iw + i) * par.nreq ..][0..par.nreq]);
                }
                if (!checkAgainstExtension(par, proof.y_ldt, idx, yc, ext, rest)) {
                    return error.LowDegreeCheckFailed;
                }
            }

            {
                innerProductVector(a, par, b.len, llterm, alphal, lqc, alphaq);

                @memcpy(yc, proof.req[Param.idot * par.nreq ..][0..par.nreq]);
                for (0..par.nwqrow) |i| {
                    extendARow(af, par, a, i, aext, rest);
                    const req_row = proof.req[(Param.iw + i) * par.nreq ..][0..par.nreq];
                    for (yc, idx, req_row) |*y, col, wv| {
                        y.* = y.add(af[par.dblock + col].mul(wv));
                    }
                }
                if (!checkAgainstExtension(par, proof.y_dot, idx, yc, ext, rest)) {
                    return error.DotCheckFailed;
                }

                var want_dot = F.zero;
                for (b, alphal) |bv, av| want_dot = want_dot.add(bv.mul(av));
                var proof_dot = F.zero;
                for (proof.y_dot[par.nreq..][0..par.w]) |v| proof_dot = proof_dot.add(v);
                if (!want_dot.eql(proof_dot)) return error.WrongDotProduct;
            }

            {
                @memcpy(yc, proof.req[Param.iquad * par.nreq ..][0..par.nreq]);
                const iqx = par.iq();
                const iqy = iqx + par.nqtriples;
                const iqz = iqy + par.nqtriples;
                for (0..par.nqtriples) |i| {
                    const rx = proof.req[(iqx + i) * par.nreq ..][0..par.nreq];
                    const ry = proof.req[(iqy + i) * par.nreq ..][0..par.nreq];
                    const rz = proof.req[(iqz + i) * par.nreq ..][0..par.nreq];
                    for (yc, rx, ry, rz) |*y, xv, yv, zv| {
                        y.* = y.add(u_quad[i].mul(zv.sub(xv.mul(yv))));
                    }
                }

                @memcpy(yquad[0..par.nreq], proof.y_quad_0);
                @memset(yquad[par.nreq..][0..par.w], F.zero);
                @memcpy(yquad[par.block..], proof.y_quad_2);
                if (!checkAgainstExtension(par, yquad, idx, yc, ext, rest)) {
                    return error.QuadraticCheckFailed;
                }
            }
        }

        /// Cuts the first `n` elements off `rest`; used to carve the
        /// scratch buffers of a call out of one allocation.
        fn take(rest: *[]F, n: usize) []F {
            defer rest.* = rest.*[n..];
            return rest.*[0..n];
        }

        /// Extends `y` into `ext` spanning the full row length and
        /// compares its values at the opened columns with `yc`.
        fn checkAgainstExtension(par: Param, y: []const F, idx: []const usize, yc: []const F, ext: []F, scratch: []F) bool {
            F.extend(ext, y, scratch);
            for (idx, yc) |col, want| {
                if (!ext[par.dblock + col].eql(want)) return false;
            }
            return true;
        }

        /// Combines all constraints into one vector A of per-witness-slot
        /// coefficients: random combinations of the linear constraints,
        /// plus consistency terms binding the quadratic-row copies to the
        /// witnesses they duplicate.
        fn innerProductVector(
            a: []F,
            par: Param,
            nl: usize,
            llterm: []const LinearTerm,
            alphal: []const F,
            lqc: []const QuadraticConstraint,
            alphaq: []const F,
        ) void {
            assert(a.len == par.nwqrow * par.w);
            @memset(a, F.zero);

            for (llterm) |term| {
                assert(term.w < par.nw and term.c < nl);
                a[term.w] = a[term.w].add(term.k.mul(alphal[term.c]));
            }

            const ax = par.nwrow * par.w;
            const ay = ax + par.nqtriples * par.w;
            const az = ay + par.nqtriples * par.w;

            for (lqc, 0..) |l, i| {
                assert(l.x < par.nw and l.y < par.nw and l.z < par.nw);
                a[ax + i] = a[ax + i].add(alphaq[3 * i]);
                a[l.x] = a[l.x].sub(alphaq[3 * i]);
                a[ay + i] = a[ay + i].add(alphaq[3 * i + 1]);
                a[l.y] = a[l.y].sub(alphaq[3 * i + 1]);
                a[az + i] = a[az + i].add(alphaq[3 * i + 2]);
                a[l.z] = a[l.z].sub(alphaq[3 * i + 2]);
            }
        }

        /// Writes the constraint-vector row for witness block `i` to
        /// `out`: zero blinding columns followed by the A window, extended
        /// to out.len codeword evaluations.
        /// `aext` stages the row basis and needs `block` elements.
        fn extendARow(out: []F, par: Param, a: []const F, i: usize, aext: []F, scratch: []F) void {
            @memset(aext[0..par.nreq], F.zero);
            @memcpy(aext[par.nreq..par.block], a[i * par.w ..][0..par.w]);
            F.extend(out, aext[0..par.block], scratch);
        }

        fn addScaled(dst: []F, k: F, src: []const F) void {
            for (dst, src) |*y, x| y.* = y.add(k.mul(x));
        }

        /// Leaf digest for one committed column: SHA-256 of the nonce
        /// followed by the column's `count` elements at the given start
        /// and stride.
        /// Prover and verifier must hash identically, so this lives in
        /// one place.
        fn leafHash(nonce: *const [nonce_len]u8, elems: []const F, start: usize, stride: usize, count: usize) Digest {
            var h = Sha256.init(.{});
            h.update(nonce);
            for (0..count) |i| {
                h.update(&elems[start + i * stride].toBytes());
            }
            var out: Digest = undefined;
            h.final(&out);
            return out;
        }
    };
}

const Fp128 = @import("field.zig").Fp128;

fn hashTerms(comptime F: type, llterm: []const Ligero(F).LinearTerm) Digest {
    var h = Sha256.init(.{});
    for (llterm) |term| {
        var b: [16]u8 = undefined;
        std.mem.writeInt(u64, b[0..8], term.c, .little);
        std.mem.writeInt(u64, b[8..16], term.w, .little);
        h.update(&b);
        h.update(&term.k.toBytes());
    }
    var out: Digest = undefined;
    h.final(&out);
    return out;
}

test "prove and verify over Fp128" {
    const gpa = std.testing.allocator;
    const L = Ligero(Fp128);

    // Witness: W[2] = W[0]*W[1], one extra linear relation, some slack.
    const witness = [6]Fp128{ .fromInt(3), .fromInt(4), .fromInt(12), .fromInt(5), .fromInt(7), .fromInt(35) };
    const lqc = [2]QuadraticConstraint{ .{ .x = 0, .y = 1, .z = 2 }, .{ .x = 3, .y = 4, .z = 5 } };
    const llterm = [3]L.LinearTerm{
        .{ .c = 0, .w = 0, .k = .fromInt(1) },
        .{ .c = 0, .w = 1, .k = .fromInt(1) },
        .{ .c = 1, .w = 3, .k = .fromInt(2) },
    };
    const b = [2]Fp128{ .fromInt(7), .fromInt(10) };
    const hash = hashTerms(Fp128, &llterm);

    const param = try L.Param.init(witness.len, lqc.len, 4, 2, 64);
    var prng = std.Random.DefaultPrng.init(42);

    var prover = try L.Prover.init(gpa, param);
    defer prover.deinit(gpa);

    var tp = Transcript.init("ligero test");
    const commitment = prover.commit(&tp, &witness, 0, &lqc, prng.random());
    var proof = try prover.prove(gpa, &tp, b.len, &llterm, hash, &lqc);
    defer proof.deinit(gpa);

    var tv = Transcript.init("ligero test");
    tv.writeBytes(&commitment.root);
    try L.verify(gpa, param, commitment, proof, &tv, &llterm, hash, &b, &lqc);

    // A wrong right-hand side must be rejected.
    var tb = Transcript.init("ligero test");
    tb.writeBytes(&commitment.root);
    const bad_b = [2]Fp128{ .fromInt(8), .fromInt(10) };
    try std.testing.expectError(
        error.WrongDotProduct,
        L.verify(gpa, param, commitment, proof, &tb, &llterm, hash, &bad_b, &lqc),
    );

    // A tampered opened column must fail the Merkle check.
    proof.req[0] = proof.req[0].add(.one);
    var tm = Transcript.init("ligero test");
    tm.writeBytes(&commitment.root);
    try std.testing.expectError(
        error.MerkleCheckFailed,
        L.verify(gpa, param, commitment, proof, &tm, &llterm, hash, &b, &lqc),
    );
}

test "prove and verify over GF(2^128) with subfield witnesses" {
    const gpa = std.testing.allocator;
    const L = Ligero(Gf2_128);

    // All witnesses in the subfield; z = x*y stays in the subfield.
    const x = Gf2_128.inj(1234);
    const y = Gf2_128.inj(4321);
    const witness = [4]Gf2_128{ x, y, x.mul(y), Gf2_128.inj(77) };
    const lqc = [1]QuadraticConstraint{.{ .x = 0, .y = 1, .z = 2 }};
    const llterm = [1]L.LinearTerm{.{ .c = 0, .w = 3, .k = Gf2_128.one }};
    const b = [1]Gf2_128{Gf2_128.inj(77)};
    const hash = hashTerms(Gf2_128, &llterm);

    // block_enc = 36 gives block = 6 and w = 4, so the single witness
    // row's payload is exactly the witness and the row is subfield-only.
    const param = try L.Param.init(witness.len, lqc.len, 4, 2, 36);
    try std.testing.expectEqual(4, param.w);
    var prng = std.Random.DefaultPrng.init(7);

    var prover = try L.Prover.init(gpa, param);
    defer prover.deinit(gpa);

    var tp = Transcript.init("ligero gf2 test");
    const commitment = prover.commit(&tp, &witness, witness.len, &lqc, prng.random());
    var proof = try prover.prove(gpa, &tp, b.len, &llterm, hash, &lqc);
    defer proof.deinit(gpa);

    // With the boundary covering every witness row, the opened witness
    // row entries stay in the subfield.
    for (0..param.nreq) |k| {
        try std.testing.expect(proof.req[(L.Param.iw + 0) * param.nreq + k].isInSubfield());
    }

    var tv = Transcript.init("ligero gf2 test");
    tv.writeBytes(&commitment.root);
    try L.verify(gpa, param, commitment, proof, &tv, &llterm, hash, &b, &lqc);
}
