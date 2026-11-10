# The same three functions, proved seven ways

This directory is the experiment behind the comparison table in the crate
README. It exists to answer one question honestly:

> If a Rust crate can carry its own formal verification, how does that compare
> with the tools people already use — including SPARK, the one that made
> "proof in the code" respectable?

Seven tools verify the **same three functions**. Four of them are Rust tools,
two are general proof assistants, and one is SPARK itself. Everything here is
reproducible from this directory. An eighth entry, Ferrocene, is in the table as
well — not as a verifier, but as the qualified *compiler* that answers the other
half of a safety case, and the difference between the two halves is explained
below.

## The example set

Three functions, chosen so that each one stresses a different part of a
verifier:

| Function | What it stresses |
| --- | --- |
| `sat_add` | A guard that makes an otherwise-overflowing `+` safe. A wrong branch order silently wraps. |
| `clamp` | Branch coverage: all three arms must be proved, not the one a test ran. |
| `sum_to` | A loop. Deciding it needs an **induction hypothesis**, not unwinding to a fixed depth. |

`target.rs` is the Rust source, with `discharge` contracts as doc comments.
Every other file is the same three functions written the way that tool wants
them.

## The result

Every *verifier* in this table verified all three functions. That is the fair
baseline, and it matters: a comparison where the home tool wins because the
others were configured badly would be worthless. The two non-verifier rows are
there as controls, not as competitors.

| Tool | Kind | Verified | Caught the swapped branches | Caught the wrong loop body | Where the contract lives |
| --- | --- | --- | --- | --- | --- |
| plain `rustc` | no verification | — | no (release build returns `0`) | no | — |
| Ferrocene | **qualified** compiler (TÜV SÜD) | not applicable — a compiler, not a verifier | no | no | — |
| `discharge` | in-crate decision procedure | 3/3 | yes, concrete witness | yes, invariant not preserved | doc comments in the same file |
| Kani 0.68.0 | bounded model check (CBMC) | 3/3 | yes | yes (with `unwind(10)`) | a separate `#[cfg(kani)]` harness module |
| Verus | SMT (Z3), deductive | 4 verified | yes | yes | `requires`/`ensures`/`decreases` attributes |
| Prusti 0.2.2 | SMT (Viper), deductive | 3/3 | yes | yes | `#[requires]`/`#[ensures]` + `body_invariant!` |
| SPARK (`gnatprove` 16.1) | SMT (CVC5 et al.), deductive | 9 checks | yes, with counterexample | yes | `Pre`/`Post` aspects, in the Ada spec |
| Coq 8.20.1 | interactive kernel | 3 theorems | yes (once the model is right) | yes | a separate `.v` file, about a **model** |
| Lean 4.35 | interactive kernel | 3 theorems | yes (once the model is right) | yes | a separate `.lean` file, about a **model** |

So the headline is not "the others fail". They do not. The headline is *what
each one is actually proving*, and what that costs.

## What the annotations cost

Measured on this example set, counting only the lines a human had to write
beyond the plain function bodies (`plain.rs` is 6 lines for all three):

| Tool | Total lines | Lines that are specification or proof | Notes |
| --- | --- | --- | --- |
| `discharge` | 47 | 14 contract lines | one doc comment per obligation, next to the code |
| Kani | 39 | 28 harness lines | the harness restates every signature; nothing keeps it in sync with the function |
| Verus | 40 | 7 spec lines | plus `decreases` on every loop |
| Prusti | 26 | 7 spec lines | plus `body_invariant!` on every loop |
| SPARK | 54 | 7 spec lines | split across `.ads` (spec) and `.adb` (body); loops need `Loop_Invariant` **and** `Loop_Variant` |
| Coq | 46 | 19 proof lines | plus a hand-written model of the arithmetic |
| Lean | 46 | 22 proof lines | plus a hand-written model of the arithmetic |

The `discharge` contract count is the honest comparison point for "verification
in the code": 14 lines, in the same file, immediately above the function they
constrain. Kani needs a harness that duplicates the signature; Coq and Lean
need a model and a proof, both in another file.

## The finding that actually matters: model drift

Coq and Lean do not prove anything about the Rust code. They prove theorems
about a **model** that a human transcribed by hand. That transcription is where
the risk lives, and it is easy to demonstrate.

The first version of `coq/example.v` modelled the `u16` add as ordinary
mathematical integers:

```coq
Definition sat_add_buggy (a b : Z) : Z :=
  if Z.gtb a (MAX - b) then a + b else MAX.
```

That is the **buggy** function, with the branches swapped. And `coqc` proved
the false statement about it, because in unbounded `Z` the sum never wraps, so
the branch that overflows on real `u16` cannot overflow in the model. The
proof was correct and the conclusion was wrong.

The committed version fixes the model by making the wrap explicit
(`Z.modulo (a + b) 65536`), and then the same false theorem is **not**
provable. The model is the proof's weakest link, and nothing in Coq or Lean
checks it against the code.

`discharge` has no model to drift, because its frontend reads the **MIR that
`rustc` actually emitted** for the function. There is no transcription step, so
there is no transcription to get wrong. The obligations are about the machine's
wrapping `u16` add because that is what the MIR contains.

This is the real reason "verification that lives in the code" is a different
thing from "verification of a model of the code". It is not about taste.

## What `discharge` is better at, and what it is not

Better here:

- **No transcription.** Contracts are doc comments on the function; the
  obligations are generated from the compiled MIR. Nothing to keep in sync.
- **Panics are proved too, not assumed away.** `sat_add` discharges 4
  obligations *and rules out 2 panics*; `sum_to` discharges 5 and rules out 2.
  The overflow that a plain release build silently wraps into `0` is an
  obligation here.
- **No external process, no allocator, `no_std`.** The prover is code in the
  artifact. The comparison tools are all host-side binaries you install,
  configure, and trust; `gnatprove` alone pulls in CVC5, Alt-Ergo, Why3 and a
  bundled Z3.
- **Speed.** `discharge` decided all three functions in about 0.01 s. Kani and
  Prusti take seconds to minutes, dominated by CBMC and by JVM/Viper startup.

Not better, and worth saying plainly:

- **No interactive proof.** `discharge` is a decision procedure over bit-vector
  arithmetic plus a bounded Hoare logic. You cannot state a property that needs
  induction over an unbounded domain, or a higher-order lemma. Coq and Lean can.
  When the BDD arena fills, the engine says `Unknown` rather than guessing — the
  scaling wall is real and documented in the main README.
- **No certification.** This is research-grade. It has no qualification
  evidence and no independent review. SPARK's advantage is not that Ada is a
  better language; it is that the toolchain has been qualified and audited for
  decades. Nothing here changes that.
- **Pointers, aliasing and concurrency are out of scope**, as the main README
  states. `mem` models a bounded array by integer index.

The honest summary: `discharge` removes the *transcription* risk and the
*external-toolchain* cost that the other approaches carry, and it does so in
`no_std` code that ships inside the artifact. It does not remove the need for
qualification, and it does not replace an interactive prover when the property
needs one.

## Ferrocene: a qualified compiler, which is a different axis

Ferrocene is in the table for completeness, and it is the one entry whose
"Verified" column is not applicable. It does not prove the three functions, and
it never claims to. It is the TÜV SÜD–qualified Rust toolchain — ISO 26262
ASIL D, IEC 61508 SIL 3 (with support for customer certification toward SIL 4),
and IEC 62304 Class C, with a certified subset of the core library — and what it
qualifies is the **compiler**, not the program.

That distinction is the whole point of listing it. `discharge` and Ferrocene are
not competitors; they are the two halves of what a certified Rust safety case
needs:

- Ferrocene answers *"can I trust the toolchain that produced this binary?"*
  A qualified compiler removes the need to qualify the compiler yourself, which
  is otherwise an enormous cost in any regulated project.
- `discharge` answers *"is the program's logic correct?"* Ferrocene does not
  answer that at all. Compile the swapped-branch `sat_add` with Ferrocene and it
  builds cleanly: Ferrocene is a downstream of `rustc`, and a release profile
  turns off the overflow check that would catch it, so the function returns `0`
  exactly as plain `rustc` does (measured here: `sat_add(32768, 32768) = 0`). A
  qualified compiler for a correct language subset still compiles a logic bug
  faithfully.

So the honest reading of the table is that Ferrocene and `discharge` are
complementary, and the repository already treats them that way: `tools/ferrocene/`
is gate 3 in `scripts/gate.sh`, and it checks that the qualified compiler accepts
the same `no_std` sources for `thumbv7em-none-eabihf` — including
`examples/bare_metal.rs`, which calls the decision procedure, so it is the
*prover* that the qualified compiler is shown to accept.

Two things worth stating plainly, because they are the traps in this area:

1. **A qualified compiler is not a qualified verifier.** Building with Ferrocene
   confers no qualification on `discharge`'s engine, which is outside Ferrocene's
   qualification scope. `discharge`'s own README says it has no qualification
   evidence; that stays true after a green Ferrocene build.
2. **Ferrocene cannot be installed programmatically.** Its release archives
   require authentication through the customer portal, so `tools/ferrocene/run.sh`
   exits `2` and `gate.sh` reports and skips when no toolchain is present. A
   skipped oracle is not a passed oracle, and the script distinguishes "absent"
   (`2`) from "failed" (`1`) so the two are never confused. In this environment
   Ferrocene is absent, which is why its row carries no verification result.

The comparison that matters for the "verification in the code" idea is still the
one between `discharge` and the five verifiers above it. Ferrocene is on the
page because leaving it out would let a reader think qualification was
unaddressed, and because the honest story is that `discharge` supplies the
*logic* half that Ferrocene deliberately does not.

## The bug files

`bugs/` holds the same three functions with two real defects, so that each
tool can be shown to **refuse** a false claim rather than only to agree with
true ones:

- `bugs/target.rs`, `bugs/kani.rs`, `bugs/verus.rs`, `bugs/prusti.rs` — the
  swapped-branch `sat_add` and the wrong-body `sum_to`, per Rust tool.
- `bugs/loop.rs` — the wrong loop body alone, for `discharge`.
- `bugs/coq/teeth.v`, `bugs/lean/teeth.lean` — both false claims, under the
  **same model** that proves the correct versions, so the difference is the
  code and not the encoding.
- `bugs/spark/` — both defects, in the same SPARK project layout.

Every one of the seven tools caught both defects. The specific evidence:

- `discharge`: `panic: attempt to compute ... which would overflow — v1:u16 = 327…`
- Kani: two harnesses `Status: FAILURE`
- Verus: `possible arithmetic underflow/overflow` and
  `invariant not satisfied at end of loop body`
- Prusti: `loop invariant might not hold after a loop iteration that preserves
  the loop condition`
- SPARK: `high: postcondition might fail` with `e.g. when A = Word'Last`
- Coq / Lean: `Cannot find witness` / `omega could not prove the goal`

## Reproducing

`discharge` needs a nightly `rustc` for the MIR frontend (the repo pins one).
The other tools are external, and none of them is a dependency of the crate.

```console
# discharge -- correct, then the two bug files
DISCHARGE_RUSTC=$(rustup which --toolchain nightly-2026-08-21 rustc) \
  cargo run -q --features std --example mir_coverage -- examples/comparison/target.rs
cargo run -q --features std --example mir_coverage -- examples/comparison/bugs/target.rs
cargo run -q --features std --example mir_coverage -- examples/comparison/bugs/loop.rs

# Kani -- copy the harness into a crate with `kani` on the path
cargo kani --version        # 0.68.0
# Verus
verus examples/comparison/verus.rs
# Prusti 0.2.2 -- needs its pinned nightly-2023-08-15 and a JDK 21
prusti-rustc --edition 2021 --crate-type lib examples/comparison/prusti.rs
# Coq -- exit 0 for the example, non-zero for the bug file
coqc examples/comparison/coq/example.v
coqc examples/comparison/bugs/coq/teeth.v
# Lean 4, core only, no Mathlib
lean examples/comparison/lean/example.lean
lean examples/comparison/bugs/lean/teeth.lean
# SPARK -- needs `alr install gnatprove`; `obj/` is generated and ignored
gnatprove -P examples/comparison/spark/example.gpr --level=2
gnatprove -P examples/comparison/bugs/spark/example.gpr --level=2
# Ferrocene -- a qualified compiler, not a verifier; absent without a
# customer-portal token, in which case run.sh exits 2 and gate.sh skips it
sh tools/ferrocene/run.sh
```

Tool versions used for the table: `rustc` 1.99.1 (nightly 2026-08-21 for the
MIR frontend), Kani 0.68.0, Verus (2026-08 build), Prusti 0.2.2 (2023-08-22),
Coq 8.20.1, Lean 4.35.0, `gnatprove` FSF 16.1.0.
