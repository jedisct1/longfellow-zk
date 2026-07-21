//! The encrypted sumcheck argument.
//!
//! The prover walks the circuit layer by layer, running the classic
//! sumcheck protocol for the quadratic wire relation, but every field
//! element that would be revealed is blinded by subtracting a one-time pad
//! value.
//! The verifier cannot check such a proof directly; instead `constraints`
//! replays the transcript symbolically and emits linear and quadratic
//! constraints over the witness vector (private inputs followed by the
//! pad) which the Ligero commitment then proves.
//!
//! Each degree-2 round polynomial is represented by its evaluations at 0
//! and at P2 (2 in odd fields, inj(2) in GF(2^128)); the evaluation at 1
//! is implied by the running claim.

const std = @import("std");
const Allocator = std.mem.Allocator;
const assert = std.debug.assert;

const circuit = @import("circuit.zig");
const ligero = @import("ligero.zig");
const Transcript = @import("Transcript.zig");

/// Number of initial challenges that are generated and discarded, and the
/// size of the challenge block from which the output bindings are drawn.
pub const max_bindings = 40;

pub fn Sumcheck(comptime F: type) type {
    return struct {
        const Circuit = circuit.Circuit(F);

        /// A round polynomial, blinded: evaluations at 0 and P2 minus the
        /// corresponding pad values.
        pub const Poly = struct {
            p0: F,
            p2: F,
        };

        pub const LayerProof = struct {
            /// 2*logw blinded polynomials, indexed by 2*round + hand.
            evals: []Poly,
            vl: F,
            vr: F,
        };

        pub const Proof = struct {
            /// Backing storage for every layer's evals.
            evals: []Poly,
            layers: []LayerProof,

            pub fn deinit(p: *Proof, gpa: Allocator) void {
                gpa.free(p.evals);
                gpa.free(p.layers);
                p.* = undefined;
            }
        };

        /// The one-time pad, stored flat in witness order: for every layer,
        /// 4*logw polynomial pads (p0 and p2 for each round and hand),
        /// then vl, vr, vl*vr.
        /// The values are a view of caller-owned memory.
        pub const Pad = struct {
            values: []const F,

            /// Fills `values`, which must hold padLength(c) elements, with
            /// a fresh random pad.
            pub fn generate(values: []F, c: Circuit, random: std.Random) Pad {
                assert(values.len == padLength(c));
                var base: usize = 0;
                for (c.layers) |layer| {
                    for (values[base..][0 .. 4 * layer.logw + 2]) |*v| {
                        v.* = F.random(random);
                    }
                    const vl = values[base + 4 * layer.logw];
                    const vr = values[base + 4 * layer.logw + 1];
                    values[base + 4 * layer.logw + 2] = vl.mul(vr);
                    base += 4 * layer.logw + 3;
                }
                return .{ .values = values };
            }
        };

        /// One term of a linear constraint: coeff * w[index].
        pub const Term = struct {
            index: usize,
            coeff: F,
        };

        /// The linear constraint k + sum(coeff * w[index]) = 0.
        pub const Linear = struct {
            k: F,
            terms: []Term,
        };

        /// The quadratic constraint w[x] * w[y] = w[z], shared with the
        /// commitment layer that ultimately proves it.
        pub const Quadratic = ligero.QuadraticConstraint;

        pub const Constraints = struct {
            /// Length of the witness vector: private inputs followed by
            /// the pad.
            num_vars: usize,
            /// Backing storage for every linear constraint's terms.
            terms: []Term,
            linear: []Linear,
            quadratic: []Quadratic,

            pub fn deinit(cs: *Constraints, gpa: Allocator) void {
                gpa.free(cs.terms);
                gpa.free(cs.linear);
                gpa.free(cs.quadratic);
                cs.* = undefined;
            }
        };

        /// Number of one-time pad elements for this circuit.
        pub fn padLength(c: Circuit) usize {
            return layerPadBase(c, c.layers.len);
        }

        /// Length of the full witness vector (private inputs + pad).
        pub fn witnessLength(c: Circuit) usize {
            return c.ninputs - c.npub_in + padLength(c);
        }

        fn layerPadBase(c: Circuit, j: usize) usize {
            var n: usize = 0;
            for (c.layers[0..j]) |layer| n += 4 * layer.logw + 3;
            return n;
        }

        /// The per-layer quadratic constraints tying each layer's claim
        /// pads (vl, vr) to their committed product.
        /// This is the one place that knows where the claim pads sit in
        /// the witness vector; `constraints` and the ZK layer both rely
        /// on it.
        pub fn quadraticConstraints(gpa: Allocator, c: Circuit) Allocator.Error![]Quadratic {
            const num_private = c.ninputs - c.npub_in;
            const lqc = try gpa.alloc(Quadratic, c.layers.len);
            var base = num_private;
            for (c.layers, lqc) |layer, *q| {
                const vl = base + 4 * layer.logw;
                q.* = .{ .x = vl, .y = vl + 1, .z = vl + 2 };
                base += 4 * layer.logw + 3;
            }
            return lqc;
        }

        /// Reusable per-layer working memory, allocated once per prove or
        /// constraints call and sized by the largest layer.
        const Scratch = struct {
            slab: []F,
            eq0: []F,
            eq1: []F,
            vl: []F,
            vr: []F,
            dense: []F,
            entries: []Entry,

            fn init(gpa: Allocator, c: Circuit, max_wires: usize) Allocator.Error!Scratch {
                var max_logg = c.logNumOutputs();
                var max_quads: usize = 0;
                for (c.layers) |layer| {
                    assert(layer.logw <= max_bindings);
                    max_logg = @max(max_logg, layer.logw);
                    max_quads = @max(max_quads, layer.quads.len);
                }
                const max_eq = std.math.shl(usize, 1, max_logg);
                const slab = try gpa.alloc(F, 2 * max_eq + 3 * max_wires);
                errdefer gpa.free(slab);
                const entries = try gpa.alloc(Entry, max_quads);
                return .{
                    .slab = slab,
                    .eq0 = slab[0..max_eq],
                    .eq1 = slab[max_eq..][0..max_eq],
                    .vl = slab[2 * max_eq ..][0..max_wires],
                    .vr = slab[2 * max_eq + max_wires ..][0..max_wires],
                    .dense = slab[2 * max_eq + 2 * max_wires ..][0..max_wires],
                    .entries = entries,
                };
            }

            fn deinit(s: *Scratch, gpa: Allocator) void {
                gpa.free(s.slab);
                gpa.free(s.entries);
                s.* = undefined;
            }
        };

        /// Runs the encrypted sumcheck prover.
        /// `wires` is the output of `Circuit.evaluate`; the transcript
        /// must already contain the statement.
        /// Writes the blinded proof into the transcript as it is produced.
        pub fn prove(
            gpa: Allocator,
            t: *Transcript,
            c: Circuit,
            wires: []const []F,
            pad: Pad,
        ) Allocator.Error!Proof {
            var g_bufs: [2][max_bindings]F = undefined;
            var g: [2]std.ArrayList(F) = .{ .initBuffer(&g_bufs[0]), .initBuffer(&g_bufs[1]) };
            initialChallenges(t, c, &g);

            var max_wires: usize = 0;
            for (wires[1..]) |w| max_wires = @max(max_wires, w.len);
            var scratch = try Scratch.init(gpa, c, max_wires);
            defer scratch.deinit(gpa);

            var total_evals: usize = 0;
            for (c.layers) |layer| total_evals += 2 * layer.logw;
            const evals_pool = try gpa.alloc(Poly, total_evals);
            errdefer gpa.free(evals_pool);
            const proof_layers = try gpa.alloc(LayerProof, c.layers.len);

            var off: usize = 0;
            var pad_base: usize = 0;
            for (c.layers, 0..) |layer, j| {
                const alpha = t.generateField(F);
                const beta = t.generateField(F);
                const entries = boundQuad(c, j, g[0].items, g[1].items, alpha, beta, scratch);

                g[0].clearRetainingCapacity();
                g[1].clearRetainingCapacity();
                const evals = evals_pool[off..][0 .. 2 * layer.logw];
                off += evals.len;
                proof_layers[j] = proveLayer(t, entries, wires[j + 1], layer.logw, pad, pad_base, &g, scratch, evals);
                pad_base += 4 * layer.logw + 3;
            }
            return .{ .evals = evals_pool, .layers = proof_layers };
        }

        fn proveLayer(
            t: *Transcript,
            entries: []Entry,
            wires_in: []const F,
            logw: usize,
            pad: Pad,
            pad_base: usize,
            g: *[2]std.ArrayList(F),
            scratch: Scratch,
            evals: []Poly,
        ) LayerProof {
            assert(evals.len == 2 * logw);

            var vl = scratch.vl;
            var vr = scratch.vr;
            @memcpy(vl[0..wires_in.len], wires_in);
            @memcpy(vr[0..wires_in.len], wires_in);
            var vl_len = wires_in.len;
            var vr_len = wires_in.len;

            const scratch_dense = scratch.dense;

            const one_minus_p2 = F.one.sub(F.p2);

            for (0..logw) |round| {
                for (0..2) |hand| {
                    var p0 = F.zero;
                    for (entries) |e| {
                        const kh = if (hand == 0) e.l else e.r;
                        const ko = if (hand == 0) e.r else e.l;
                        if (kh & 1 == 0) {
                            p0 = p0.add(e.v.mul(at(vl, vl_len, kh)).mul(at(vr, vr_len, ko)));
                        }
                    }

                    // Evaluate at P2 by binding a scratch copy; vl itself
                    // is only bound by the real challenge below.
                    @memcpy(scratch_dense[0..vl_len], vl[0..vl_len]);
                    const vl_p2_len = bindDense(scratch_dense, vl_len, F.p2, one_minus_p2);
                    var p2 = F.zero;
                    for (entries) |e| {
                        const kh = if (hand == 0) e.l else e.r;
                        const ko = if (hand == 0) e.r else e.l;
                        const bound_v = if (kh & 1 == 0) e.v.mul(one_minus_p2) else e.v.mul(F.p2);
                        p2 = p2.add(bound_v.mul(at(scratch_dense, vl_p2_len, kh >> 1)).mul(at(vr, vr_len, ko)));
                    }

                    const idx = pad_base + 4 * round + 2 * hand;
                    const blinded: Poly = .{
                        .p0 = p0.sub(pad.values[idx]),
                        .p2 = p2.sub(pad.values[idx + 1]),
                    };
                    evals[2 * round + hand] = blinded;
                    t.writeField(F, blinded.p0);
                    t.writeField(F, blinded.p2);
                    const challenge = t.generateField(F);
                    g[hand].appendAssumeCapacity(challenge);

                    vl_len = bindDense(vl, vl_len, challenge, F.one.sub(challenge));
                    bindEntries(entries, challenge, hand);

                    std.mem.swap([]F, &vl, &vr);
                    std.mem.swap(usize, &vl_len, &vr_len);
                }
            }

            const vl_idx = pad_base + 4 * logw;
            const proof: LayerProof = .{
                .evals = evals,
                .vl = at(vl, vl_len, 0).sub(pad.values[vl_idx]),
                .vr = at(vr, vr_len, 0).sub(pad.values[vl_idx + 1]),
            };
            t.writeFieldArray(F, &.{ proof.vl, proof.vr });
            return proof;
        }

        /// Replays a proof against the transcript and produces the
        /// constraints that the commitment scheme must verify.
        /// Mirrors every transcript operation of `prove`.
        pub fn constraints(
            gpa: Allocator,
            t: *Transcript,
            c: Circuit,
            public_inputs: []const F,
            proof: Proof,
        ) Allocator.Error!Constraints {
            assert(public_inputs.len == c.npub_in);
            const num_private = c.ninputs - c.npub_in;

            var g_bufs: [2][max_bindings]F = undefined;
            var g: [2]std.ArrayList(F) = .{ .initBuffer(&g_bufs[0]), .initBuffer(&g_bufs[1]) };
            initialChallenges(t, c, &g);

            var scratch = try Scratch.init(gpa, c, 0);
            defer scratch.deinit(gpa);

            // One constraint per layer plus the final input binding, each
            // with a term count fixed by the layer shape.
            var total_terms: usize = num_private + 2;
            for (c.layers, 0..) |layer, j| {
                total_terms += 4 * layer.logw + 3 + @as(usize, if (j > 0) 2 else 0);
            }
            const terms_pool = try gpa.alloc(Term, total_terms);
            errdefer gpa.free(terms_pool);
            const linear = try gpa.alloc(Linear, c.layers.len + 1);
            errdefer gpa.free(linear);
            var off: usize = 0;

            const denom = lagrangeDenominators();

            // Claims carried between layers: concrete part and, from the
            // second layer on, one pad variable each.
            var claim0 = F.zero;
            var claim1 = F.zero;

            var pad_base = num_private;
            for (c.layers, 0..) |layer, j| {
                const alpha = t.generateField(F);
                const beta = t.generateField(F);
                const entries = boundQuad(c, j, g[0].items, g[1].items, alpha, beta, scratch);

                const nterms = 4 * layer.logw + 3 + @as(usize, if (j > 0) 2 else 0);
                const terms = terms_pool[off..][0..nterms];
                off += nterms;
                var claim: Affine = .{
                    .k = claim0.add(alpha.mul(claim1)),
                    .terms = .initBuffer(terms),
                };
                if (j > 0) {
                    const prev_logw = c.layers[j - 1].logw;
                    const prev_base = pad_base - (4 * prev_logw + 3);
                    claim.terms.appendAssumeCapacity(.{ .index = prev_base + 4 * prev_logw, .coeff = F.one });
                    claim.terms.appendAssumeCapacity(.{ .index = prev_base + 4 * prev_logw + 1, .coeff = alpha });
                }

                g[0].clearRetainingCapacity();
                g[1].clearRetainingCapacity();

                for (0..layer.logw) |round| {
                    for (0..2) |hand| {
                        const hp = proof.layers[j].evals[2 * round + hand];
                        t.writeField(F, hp.p0);
                        t.writeField(F, hp.p2);
                        const challenge = t.generateField(F);
                        g[hand].appendAssumeCapacity(challenge);

                        // With p1 = claim - p0, the interpolated claim at
                        // the challenge x is
                        //   lag0(x)*p0 + lag1(x)*p1 + lag2(x)*p2
                        // = lag1(x)*claim + (lag0(x)-lag1(x))*p0 + lag2(x)*p2
                        // where p0 and p2 are the blinded proof values plus
                        // one pad variable each.
                        const l = lagrange(challenge, denom);
                        const c0 = l[0].sub(l[1]);
                        claim.scale(l[1]);
                        claim.k = claim.k.add(c0.mul(hp.p0)).add(l[2].mul(hp.p2));
                        const idx = pad_base + 4 * round + 2 * hand;
                        claim.terms.appendAssumeCapacity(.{ .index = idx, .coeff = c0 });
                        claim.terms.appendAssumeCapacity(.{ .index = idx + 1, .coeff = l[2] });

                        bindEntries(entries, challenge, hand);
                    }
                }

                var q = F.zero;
                for (entries) |e| {
                    assert(e.l == 0 and e.r == 0);
                    q = q.add(e.v);
                }

                // claim = Q * (vl + pad_vl) * (vr + pad_vr), linearized by
                // the pad_vl*pad_vr variable.
                const lp = proof.layers[j];
                const vl_idx = pad_base + 4 * layer.logw;
                claim.k = claim.k.sub(q.mul(lp.vl).mul(lp.vr));
                claim.terms.appendAssumeCapacity(.{ .index = vl_idx, .coeff = q.mul(lp.vr).neg() });
                claim.terms.appendAssumeCapacity(.{ .index = vl_idx + 1, .coeff = q.mul(lp.vl).neg() });
                claim.terms.appendAssumeCapacity(.{ .index = vl_idx + 2, .coeff = q.neg() });
                assert(claim.terms.items.len == terms.len);
                linear[j] = .{ .k = claim.k, .terms = terms };

                t.writeFieldArray(F, &.{ lp.vl, lp.vr });
                claim0 = lp.vl;
                claim1 = lp.vr;
                pad_base += 4 * layer.logw + 3;
            }

            // Final constraint: the last claims must equal the binding of
            // the inputs by G[0] and gamma-combined G[1].
            const gamma = t.generateField(F);
            const eq0 = bindeq(scratch.eq0, g[0].items);
            const eq1 = bindeq(scratch.eq1, g[1].items);

            const final_terms = terms_pool[off..][0 .. num_private + 2];
            off += final_terms.len;
            assert(off == terms_pool.len);
            var final: Affine = .{ .k = F.zero, .terms = .initBuffer(final_terms) };
            for (public_inputs, 0..) |x, i| {
                final.k = final.k.add(eq2At(eq0, eq1, gamma, i).mul(x));
            }
            for (0..num_private) |i| {
                final.terms.appendAssumeCapacity(.{
                    .index = i,
                    .coeff = eq2At(eq0, eq1, gamma, c.npub_in + i),
                });
            }
            const last_logw = c.layers[c.layers.len - 1].logw;
            const last_vl = pad_base - (4 * last_logw + 3) + 4 * last_logw;
            final.k = final.k.sub(claim0).sub(gamma.mul(claim1));
            final.terms.appendAssumeCapacity(.{ .index = last_vl, .coeff = F.one.neg() });
            final.terms.appendAssumeCapacity(.{ .index = last_vl + 1, .coeff = gamma.neg() });
            assert(final.terms.items.len == final_terms.len);
            linear[c.layers.len] = .{ .k = final.k, .terms = final_terms };

            return .{
                .num_vars = witnessLength(c),
                .terms = terms_pool,
                .linear = linear,
                .quadratic = try quadraticConstraints(gpa, c),
            };
        }

        /// bindv(EQ, challenges): the coefficient vector expressing a
        /// multilinear binding as a dot product, of size 2^challenges.len,
        /// written to `out`'s prefix and returned.
        pub fn bindeq(out: []F, challenges: []const F) []F {
            const n = std.math.shl(usize, 1, challenges.len);
            const b = out[0..n];
            b[0] = F.one;
            var len: usize = 1;
            // Building from the last challenge outward puts challenge i on
            // bit i of the index.
            var i = challenges.len;
            while (i > 0) {
                i -= 1;
                const x = challenges[i];
                const one_minus_x = F.one.sub(x);
                var k = len;
                while (k > 0) {
                    k -= 1;
                    const a = b[k];
                    b[2 * k] = one_minus_x.mul(a);
                    b[2 * k + 1] = x.mul(a);
                }
                len *= 2;
            }
            return b;
        }

        const Entry = struct {
            l: usize,
            r: usize,
            v: F,
        };

        /// The quad of one layer with assertions folded in (QZ = Q +
        /// beta*Z) and the gate dimension bound by both challenge vectors:
        /// coefficient (eq0[g] + alpha*eq1[g]) * QZ[g, l, r].
        fn boundQuad(
            c: Circuit,
            j: usize,
            g0: []const F,
            g1: []const F,
            alpha: F,
            beta: F,
            scratch: Scratch,
        ) []Entry {
            const eq0 = bindeq(scratch.eq0, g0);
            const eq1 = bindeq(scratch.eq1, g1);

            const quads = c.layers[j].quads;
            const entries = scratch.entries[0..quads.len];
            for (quads, entries) |q, *e| {
                const k = c.constants[q.v];
                const v = if (k.isZero()) beta else k;
                const gc = eq0[q.g].add(alpha.mul(eq1[q.g]));
                e.* = .{ .l = q.h0, .r = q.h1, .v = gc.mul(v) };
            }
            return entries;
        }

        /// Discards max_bindings challenges, generates max_bindings more,
        /// and appends the first logNumOutputs of them to both hands'
        /// initial binding challenge lists.
        fn initialChallenges(t: *Transcript, c: Circuit, g: *[2]std.ArrayList(F)) void {
            for (0..max_bindings) |_| _ = t.generateField(F);
            var challenges: [max_bindings]F = undefined;
            for (&challenges) |*x| x.* = t.generateField(F);

            const logv = c.logNumOutputs();
            assert(logv <= max_bindings);
            g[0].appendSliceAssumeCapacity(challenges[0..logv]);
            g[1].appendSliceAssumeCapacity(challenges[0..logv]);
        }

        fn at(arr: []const F, len: usize, i: usize) F {
            return if (i < len) arr[i] else F.zero;
        }

        /// In-place bind of a dense zero-padded array; returns the new
        /// logical length.
        fn bindDense(arr: []F, len: usize, x: F, one_minus_x: F) usize {
            const new_len = (len + 1) / 2;
            for (0..new_len) |i| {
                const a = at(arr, len, 2 * i);
                const b = at(arr, len, 2 * i + 1);
                arr[i] = one_minus_x.mul(a).add(x.mul(b));
            }
            return new_len;
        }

        /// In-place bind of sparse entries along one axis.
        fn bindEntries(entries: []Entry, x: F, hand: usize) void {
            const one_minus_x = F.one.sub(x);
            for (entries) |*e| {
                const kh = if (hand == 0) e.l else e.r;
                e.v = e.v.mul(if (kh & 1 == 0) one_minus_x else x);
                if (hand == 0) e.l = kh >> 1 else e.r = kh >> 1;
            }
        }

        /// Inverted denominators of the three Lagrange basis polynomials
        /// for the interpolation points {0, 1, P2}.
        /// Field inversions are expensive, so these are computed once per
        /// constraint replay.
        fn lagrangeDenominators() [3]F {
            const p2 = F.p2;
            return .{
                p2.invert().?,
                F.one.sub(p2).invert().?,
                p2.mul(p2.sub(F.one)).invert().?,
            };
        }

        /// Evaluations of the three Lagrange basis polynomials at x.
        fn lagrange(x: F, denom: [3]F) [3]F {
            return .{
                x.sub(F.one).mul(x.sub(F.p2)).mul(denom[0]),
                x.mul(x.sub(F.p2)).mul(denom[1]),
                x.mul(x.sub(F.one)).mul(denom[2]),
            };
        }

        /// A linear form over the witness under construction, with a
        /// fixed-capacity term list backed by its exact allocation.
        const Affine = struct {
            k: F,
            terms: std.ArrayList(Term),

            fn scale(a: *Affine, s: F) void {
                a.k = a.k.mul(s);
                for (a.terms.items) |*term| term.coeff = term.coeff.mul(s);
            }
        };

        fn eq2At(eq0: []const F, eq1: []const F, gamma: F, i: usize) F {
            return eq0[i].add(gamma.mul(eq1[i]));
        }
    };
}

const Fp128 = @import("field.zig").Fp128;
const fixtures = @import("testing.zig");

const TestSetup = struct {
    c: circuit.Circuit(Fp128),
    wires: [][]Fp128,
    /// The test vectors use a constant pad of 2 (so vl*vr entries are 4).
    pad_values: [26]Fp128,
    proof: Sumcheck(Fp128).Proof,

    fn init(gpa: Allocator) !TestSetup {
        const S = Sumcheck(Fp128);
        var c = try fixtures.sgonalCircuit(gpa);
        errdefer c.deinit(gpa);
        const wires = try c.evaluate(gpa, &fixtures.sgonal_inputs);
        errdefer circuit.Circuit(Fp128).freeWires(gpa, wires);

        var pad_values: [26]Fp128 = @splat(.fromInt(2));
        pad_values[14] = .fromInt(4);
        pad_values[25] = .fromInt(4);

        var tp = Transcript.init("sumcheck test");
        const proof = try S.prove(gpa, &tp, c, wires, .{ .values = &pad_values });
        return .{ .c = c, .wires = wires, .pad_values = pad_values, .proof = proof };
    }

    fn deinit(s: *TestSetup, gpa: Allocator) void {
        s.proof.deinit(gpa);
        circuit.Circuit(Fp128).freeWires(gpa, s.wires);
        s.c.deinit(gpa);
    }

    /// The witness vector: private inputs, then the pad.
    fn witness(s: TestSetup) [28]Fp128 {
        var w: [28]Fp128 = undefined;
        w[0] = fixtures.sgonal_inputs[2];
        w[1] = fixtures.sgonal_inputs[3];
        @memcpy(w[2..], &s.pad_values);
        return w;
    }

    fn allLinearHold(cs: Sumcheck(Fp128).Constraints, w: []const Fp128) bool {
        for (cs.linear) |lc| {
            var acc = lc.k;
            for (lc.terms) |term| acc = acc.add(term.coeff.mul(w[term.index]));
            if (!acc.isZero()) return false;
        }
        return true;
    }
};

test "constraints hold on an honest proof" {
    const gpa = std.testing.allocator;
    const S = Sumcheck(Fp128);

    var s = try TestSetup.init(gpa);
    defer s.deinit(gpa);
    try std.testing.expectEqual(26, S.padLength(s.c));

    // The verifier-side replay must generate identical challenges.
    var tv = Transcript.init("sumcheck test");
    var cs = try S.constraints(gpa, &tv, s.c, fixtures.sgonal_inputs[0..s.c.npub_in], s.proof);
    defer cs.deinit(gpa);

    try std.testing.expectEqual(2 + 26, cs.num_vars);
    try std.testing.expectEqual(3, cs.linear.len);
    try std.testing.expectEqual(2, cs.quadratic.len);

    const w = s.witness();
    try std.testing.expect(TestSetup.allLinearHold(cs, &w));
    for (cs.quadratic) |qc| {
        try std.testing.expect(w[qc.x].mul(w[qc.y]).eql(w[qc.z]));
    }
}

test "constraints fail for a tampered proof" {
    const gpa = std.testing.allocator;
    const S = Sumcheck(Fp128);

    var s = try TestSetup.init(gpa);
    defer s.deinit(gpa);

    s.proof.layers[0].evals[1].p2 = s.proof.layers[0].evals[1].p2.add(.one);

    var tv = Transcript.init("sumcheck test");
    var cs = try S.constraints(gpa, &tv, s.c, fixtures.sgonal_inputs[0..s.c.npub_in], s.proof);
    defer cs.deinit(gpa);

    const w = s.witness();
    try std.testing.expect(!TestSetup.allLinearHold(cs, &w));
}
