# Longfellow-ZK

A pure Zig implementation of the Longfellow zero-knowledge system
(`draft-google-cfrg-libzk-01`). No trusted setup, no elliptic curves in
the argument itself; SHA-256 and AES-256 are the only cryptographic
primitives.

## What a zero-knowledge proof does

A zero-knowledge proof lets someone who knows a secret convince someone who doesn't that a claim about the secret is true, without revealing the secret itself.

The party with the secret is the prover, the skeptic is the verifier, and the claim always has the same shape: there is public data `x` that both sides know, private data `w` (the witness) that only the prover knows, and an agreed-upon check `C`.

The proof establishes that `C(x, w) = 0` while telling the verifier nothing about `w` beyond that fact.

For example you can use it to prove that a digitally signed credential, such as a mobile driver's license, says what you claim it says, without showing the credential.

## Statements are circuits

The check `C` has to be written in a form the proof machinery can process, and that form is an arithmetic circuit: a computation whose only operations are addition and multiplication in a finite field (numbers modulo a prime, or a binary field like GF(2^128)).

Every value in the computation, input or intermediate, sits on a *wire*.

The circuit is organized in layers.

The input wires (public inputs first, then the private witness) feed the deepest layer.

Each layer computes a new row of wires from the row below it, and the top layer, layer 0, produces the output wires. By convention, the statement holds exactly when every output wire is zero.

So to assert `A = B`, you make the circuit compute `A - B` and route it to an output: a valid proof can only exist if that difference vanishes.

## Quads

Inside a layer, wires are computed by *quads*.

A quad is four small integers `(g, h0, h1, v)`, and despite the compact look it is just one instruction:

    out[g] += constants[v] * in[h0] * in[h1]

Here `in` is the row of wires below this layer (for the deepest layer, the circuit inputs), `out` is the row this layer produces, and `constants` is a per-circuit table of field elements; `v` is an index into that table, not the value itself.

A layer is nothing more than a list of such instructions, so each output wire ends up holding a sum of constant-weighted products of two lower wires.

Two idioms make this seemingly rigid form expressive enough for anything:

- Addition is free. Several quads naming the same `g` accumulate into the same output wire, and subtraction is multiplication by the  constant -1, which in a finite field is an ordinary element like any other.

- There is no "copy a wire" or "add a constant" instruction, only products of exactly two wires. The standard trick is to dedicate input wire 0 to the constant 1. Copying a wire `w` up one layer is then `1 * w0 * w`, and injecting a constant `k` is `k * w0 * w0`. This is why circuits here reserve `w0 = 1`.

## Ok, give me a full example

The example program below proves knowledge of a factorization of the public number 391, without revealing the factors (17 and 23).

The circuit computes `a*b - p` and exposes it as the only output, so a proof exists exactly when `a * b = p`. There are four input wires:

    +------+---------+---------+
    | wire | value   | role    |
    +------+---------+---------+
    | w0   | 1       | public  |
    | w1   | 391 (p) | public  |
    | w2   | 17  (a) | private |
    | w3   | 23  (b) | private |
    +------+---------+---------+

The constant table is `{ 1, -1 }`, written `F.one` and `F.one.neg()` in the code. The single layer contains two quads, both aimed at output wire 0:

    +--------------------------------+--------------------------------+
    | quad                           | meaning                        |
    +--------------------------------+--------------------------------+
    | .{ .g=0, .h0=2, .h1=3, .v=0 }  | out[0] +=  1 * w2 * w3 =  a*b  |
    | .{ .g=0, .h0=0, .h1=1, .v=1 }  | out[0] += -1 * w0 * w1 = -p    |
    +--------------------------------+--------------------------------+

The two contributions accumulate, so `out[0] = a*b - p`.

The second quad is the constant-one trick from the previous section: the circuit needs `p` by itself, and the only way to get it is to multiply the `p` wire by the always-one wire.

The remaining numbers describe the circuit's geometry:

- `layers[0] = .{ .logw = 2, .nw = 4, .quads = quads }`: this layer reads `nw = 4` wires from below. `logw = 2` is `ceil(log2(nw))`, the number of bits needed to address one of those wires; the sumcheck protocol binds one bit per round, so this is also a round count.
- `nv = 1`: the circuit has one output wire.
- `nc = 1`: one copy of the circuit. The format allows running many copies of the same circuit on different inputs; this implementation currently supports a single copy.
- `npub_in = 2`: the first two input wires are public. The verifier is given only those (`inputs[0..2]` in the code); `w2` and `w3` are the witness, and only a commitment to them ever leaves the prover.
- `subfield_boundary = 0`: only meaningful for GF(2^128) circuits, where a prefix of the inputs can be promised to lie in the small GF(2^16) subfield to shrink the proof. Zero promises nothing.
- `ninputs = 4`: total input wires, public and private.
- `id`: a SHA-256 hash over the whole circuit structure, computed by `computeId()`. Both sides absorb it into the proof transcript, so prover and verifier cannot silently disagree about which circuit is being proven.

## The example's code

```zig
const std = @import("std");
const longfellow = @import("longfellow");

const F = longfellow.field.Fp128;
const Zk = longfellow.zk.Zk(F);

// C(x, w) = 0 iff a * b = p, where the product p is public and the
// factors a and b stay private.
// Wires: w0 = 1 and w1 = p are public, w2 = a and w3 = b are private.
// The single output is w2*w3 - w0*w1.
fn factoringCircuit(gpa: std.mem.Allocator) !Zk.Circuit {
    const constants = try gpa.dupe(F, &.{ F.one, F.one.neg() });
    const quads = try gpa.dupe(Zk.Circuit.Quad, &.{
        .{ .g = 0, .h0 = 2, .h1 = 3, .v = 0 },
        .{ .g = 0, .h0 = 0, .h1 = 1, .v = 1 },
    });
    const layers = try gpa.alloc(Zk.Circuit.Layer, 1);
    layers[0] = .{ .logw = 2, .nw = 4, .quads = quads };

    var c: Zk.Circuit = .{
        .nv = 1,
        .nc = 1,
        .npub_in = 2,
        .subfield_boundary = 0,
        .ninputs = 4,
        .constants = constants,
        .layers = layers,
        .id = undefined,
    };
    c.id = c.computeId();
    return c;
}

pub fn main(init: std.process.Init) !void {
    const gpa = init.gpa;

    var circuit = try factoringCircuit(gpa);
    defer circuit.deinit(gpa);

    // Public inputs come first: the constant-one wire and p = 391.
    // The prover additionally knows the factorization 17 * 23.
    const inputs = [4]F{ .fromInt(1), .fromInt(391), .fromInt(17), .fromInt(23) };

    // Toy commitment parameters sized for this tiny witness; nreq is
    // the number of opened columns and drives soundness.
    const params: Zk.Parameters = .{ .nreq = 3, .block_enc = 64 };

    var seed: [std.Random.DefaultCsprng.secret_seed_length]u8 = undefined;
    init.io.random(&seed);
    var rng = std.Random.DefaultCsprng.init(seed);

    var pt = longfellow.Transcript.init("readme example");
    var proof = try Zk.prove(gpa, circuit, &inputs, &pt, params, rng.random());
    defer proof.deinit(gpa);

    var vt = longfellow.Transcript.init("readme example");
    try Zk.verify(gpa, circuit, inputs[0..2], proof, &vt, params);

    std.debug.print("proof verified ({d} bytes serialized)\n", .{Zk.proofSize(circuit, proof)});
}
```
