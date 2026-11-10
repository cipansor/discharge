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

| Tool | Kind | Verified | Caught the swapped branches | Caught the wrong loop body | Caught the wrong clamp arm | Where the contract lives |
| --- | --- | --- | --- | --- | --- | --- |
| plain `rustc` | no verification | — | no (release build returns `0`) | no | no | — |
| Ferrocene | **qualified** compiler (TÜV SÜD) | not applicable — a compiler, not a verifier | no | no | no | — |
| `discharge` | in-crate decision procedure | 3/3 | yes, concrete witness | yes, invariant not preserved | yes, concrete witness | doc comments in the same file |
| Kani 0.68.0 | bounded model check (CBMC) | 3/3 | yes | yes (with `unwind(10)`) | yes | a separate `#[cfg(kani)]` harness module |
| Verus | SMT (Z3), deductive | 4 verified | yes | yes | yes | `requires`/`ensures`/`decreases` attributes |
| Prusti 0.2.2 | SMT (Viper), deductive | 3/3 | yes | yes | yes | `#[requires]`/`#[ensures]` + `body_invariant!` |
| SPARK (`gnatprove` 16.1) | SMT (CVC5 et al.), deductive | 9 checks | yes, with counterexample | yes | yes | `Pre`/`Post` aspects, in the Ada spec |
| Coq 8.20.1 | interactive kernel | 3 theorems | yes (once the model is right) | yes | yes | a separate `.v` file, about a **model** |
| Lean 4.35 | interactive kernel | 3 theorems | yes (once the model is right) | yes | yes | a separate `.lean` file, about a **model** |

So the headline is not "the others fail". They do not. The headline is *what
each one is actually proving*, and what that costs.

## The contracts have to state the whole function, or they prove nothing

The first version of this comparison got this wrong, and it is the easiest way
to build a comparison that looks impressive and means nothing. The `sat_add`
contract was:

```rust
/// ensures: ret >= a
/// ensures: ret >= b
```

That is true of a saturating add, and it is also true of `fn sat_add(a, b) { u16::MAX }`
for *every* input — which is not a saturating add at all. A contract that a
degenerate implementation satisfies is not a specification; it is a bound. The
`clamp` contract had the same shape (`lo <= ret <= hi`), and `fn clamp(x, lo, hi) { lo }`
satisfies it for every input.

Every contract in this directory now states the whole function:

- `sat_add` — the result **is** `a + b` when the sum fits, and **is** `u16::MAX`
  when it does not.
- `clamp` — the result **is** `lo` below the range, **is** `hi` above it, and
  **is** `x` inside it, one clause per arm.
- `sum_to` — unchanged: `ret == n`, which the wrong loop body already falsified.

The check that matters is that each strengthened contract **rejects the
degenerate implementation**. That is now part of the reproduction:

```console
# `always return u16::MAX` satisfies the old bounds and must fail the new clause
sed 's/if a > u16::MAX - b { u16::MAX } else { a + b }/u16::MAX/' kani.rs > /tmp/degen.rs
# (run it under the same harness; verify_sat_add must be FAILED, the other two SUCCESSFUL)
```

Measured: with the bounds-only contract, the degenerate `sat_add` passed Kani
and `discharge`; with the full contract, Kani reports `verify_sat_add` FAILED
and `discharge` reports `postcondition — v1:u16 = 0, v2:u16 = 0`. The same holds
for `clamp` (`always return lo` is refused with a concrete witness).

This is why the table above has a third bug column. A comparison that only shows
the tools agreeing on true statements, and disagreeing on false ones, has not
shown that the contracts are strong enough to be worth proving. The bug files
now carry the **same strengthened contracts** as the correct files, so each
rejection is of the claim the correct function discharges, not of a weaker
strawman.

## What the annotations cost

Measured on this example set. The "spec or proof" column counts only the lines a
human had to write *beyond* the plain function bodies; the exact rule for each
row is given below the table, so every figure can be recomputed rather than
recalled.

| Tool | Total lines | Spec or proof lines | Notes |
| --- | --- | --- | --- |
| `discharge` | 55 | 12 contract lines | one doc comment per obligation, next to the code |
| Kani | 56 | 45 harness lines | the harness restates every signature; nothing keeps it in sync with the function |
| Verus | 51 | 12 spec lines | plus `decreases` on every loop |
| Prusti | 34 | 12 spec lines | plus `body_invariant!` on every loop |
| SPARK | 67 (`.ads` + `.adb`) | 14 spec lines | split across `.ads` (spec) and `.adb` (body); loops need `Loop_Invariant` **and** `Loop_Variant` |
| Coq | 67 (`model.v` + `example.v`) | 26 tactic lines | plus a hand-written model of the arithmetic |
| Lean | 54 (`model.lean` + `example.lean`) | 20 proof lines | plus a hand-written model of the arithmetic |

The rule behind each "spec or proof" figure, all run from this directory:

```console
grep -cE '^/// (requires|ensures|invariant|decreases):' target.rs   # discharge: 12
awk '/^#\[cfg\(kani\)\]/{f=1} f' kani.rs | grep -c .                # Kani: 45
grep -cE '^\s*(requires|ensures|invariant|decreases)\b|==>' verus.rs # Verus: 12
grep -cE '#\[(requires|ensures)|body_invariant!' prusti.rs          # Prusti: 12
grep -cE '^\s*(Pre|Post)\s*=>' spark/src/example.ads                # SPARK: 14
grep -cE '^\s*(-|\+|\*|reflexivity|lia|destruct|intros|unfold|rewrite|apply|split|constructor|induction|simpl|auto|Qed|Proof)' coq/example.v  # Coq: 26
awk '/:= by/{f=1} f' lean/example.lean | grep -c .                  # Lean: 20
```

Two things the earlier version of this table got wrong, both now fixed. It
reported `14` contract lines for `discharge` by counting *every* `///` line in
`target.rs`, which includes the four prose doc lines above the functions; the
contract clauses are 12, and that is the figure comparable to the other rows.
And the totals were stale: they predate the contracts being strengthened from
bounds to full specifications (see below), which added clauses to every tool.

The `discharge` contract count is the honest comparison point for "verification
in the code": 12 clauses, in the same file, immediately above the function they
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
checks it against the code. The model now lives in `coq/model.v` /
`lean/model.lean`, imported by the positive fixture *and* by both negative
fixtures — so the teeth cannot drift from the model they are testing, which is
the same failure one level down.

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

`bugs/` holds the same three functions with real defects, so that each tool can
be shown to **refuse** a false claim rather than only to agree with true ones:

- `bugs/target.rs`, `bugs/kani.rs`, `bugs/verus.rs`, `bugs/prusti.rs` — the
  swapped-branch `sat_add`, the wrong-arm `clamp`, and the wrong-body `sum_to`,
  per Rust tool.
- `bugs/loop.rs` — the wrong loop body alone, for `discharge`.
- `bugs/clamp.rs` — the wrong clamp arm alone, for `discharge`.
- `bugs/coq/teeth_sat_add.v` and `bugs/coq/teeth_sum_to.v` — **one false theorem
  per file**, each importing the same `coq/model.v` that proves the correct
  versions, so the difference is the code and not the encoding.
- `bugs/lean/teeth_sat_add.lean` and `bugs/lean/teeth_sum_to.lean` — the same,
  importing `lean/model.lean`.
- `bugs/spark/` — all three defects, in the same SPARK project layout.

Every one of the seven tools caught every defect. The specific evidence:

- `discharge`: `panic: attempt to compute ... which would overflow — v1:u16 = 327…`
  for the swap, `loop invariant preserved` for the loop, `postcondition` for the
  clamp arm.
- Kani: three harnesses `Status: FAILURE` (`0 successfully verified harnesses,
  3 failures`).
- Verus: `possible arithmetic underflow/overflow`, `invariant not satisfied at
  end of loop body`, and a clamp postcondition error (`1 verified, 3 errors`).
- Prusti: two `postcondition might not hold` and `loop invariant might not hold
  after a loop iteration that preserves the loop condition`.
- SPARK: `high: postcondition might fail` with `e.g. when A = Word'Last`, the
  clamp `postcondition might fail`, and `medium: loop invariant might not be
  preserved by an arbitrary iteration`.
- Coq / Lean: `Cannot find witness` / `omega could not prove the goal`.

### Why the Coq and Lean teeth are one theorem per file

`coqc` **stops at the first failed proof**. The earlier version of this
directory put both false Coq theorems in one `teeth.v`, so the loop theorem was
never reached: the non-zero exit proved only that the *first* theorem failed,
and would have gone on proving it even if the loop theorem were replaced by a
valid one. The rejection test did not isolate the failure it claimed to test.

Each false Coq theorem is now in its own compilation unit, and both are run and
their exit codes checked independently:

```console
coqc -Q coq "" coq/model.v            # exit 0
coqc -Q coq "" coq/example.v          # exit 0
coqc -Q coq "" bugs/coq/teeth_sat_add.v   # non-zero
coqc -Q coq "" bugs/coq/teeth_sum_to.v    # non-zero
```

Fixing that exposed a **second** defect in the same file, which the isolation
check is what found: the old loop theorem was stated as
`forall n, n <= 8 -> sum_to_buggy n = n` under `Open Scope Z_scope`, where
`n <= 8` for `n : nat` is a **type error**, not a proof failure. It was failing
for the wrong reason, and had been reported as "caught the loop body". The
committed version states the theorem over `nat` with no `Z_scope` in play, so
the failure is the genuine unprovable goal (`Attempt to save an incomplete
proof`).

Lean reports *all* errors in a file rather than stopping at the first, so it did
not have Coq's masking defect; the split is kept anyway so that each rejection
is evidence about one claim, and so the two tools stay comparable.

### The teeth are mutation-checked

A rejection is only evidence if it fails *for the reason it names*. The repo's
own rule (see `AGENTS.md`, "Teeth have to isolate the guard they claim to
test") is that before trusting a rejection test you remove the defect and
confirm the test passes. The first version of the split Coq and Lean teeth did
**not** satisfy this: their proof scripts were tailored to the buggy
definition, so correcting the definition broke the *script* rather than the
*proof*, and the "rejection" was an artifact of the script's shape. Both are now
written so the same script runs against the correct and the buggy definition,
and correcting the definition makes the file compile. Verified by mutation:

```console
# correct the swapped branches; the file must now compile
sed 's/then add_eng a b else MAX/then MAX else add_eng a b/' \
    bugs/coq/teeth_sat_add.v > /tmp/mut.v && coqc -Q coq "" /tmp/mut.v   # exit 0
# correct the loop body (+2 -> +1); the file must now compile
sed 's/S (S (sum_to_buggy k))/S (sum_to_buggy k)/' \
    bugs/coq/teeth_sum_to.v > /tmp/mut.v && coqc -Q coq "" /tmp/mut.v    # exit 0
```

## The gate: the fixtures are re-run, not remembered

Everything above was, for a while, verified by hand exactly once, and the prose
was the only record. That is the failure the repo names explicitly — a one-off
verification is not a gate, and only a gate survives the next change — so
`tools/comparison/run.sh` (gate 13 in `scripts/gate.sh`) re-runs the cheap,
hermetic half on every gate run: `discharge` on the positive fixture and all three
bug fixtures, the degenerate implementations, and Coq and Lean on the positive
fixture and both teeth including the mutations. The external provers (Kani, Verus,
Prusti, SPARK) keep their own CI jobs, where their toolchains are installed.

The `discharge` half is a driver, `examples/comparison_check.rs`, and it asserts
the per-function `FnOutcome` rather than scraping `mir_coverage`'s summary. That
choice is the whole point. The summary line counts only `Verified`, so `Failed`,
`Incomplete` and `Skipped` all leave it at `decided 0 of 1` — and the first version
of the gate asserted exactly that line, which meant a fixture whose contract had
become **unreadable** would still read `decided 0 of 1` and be reported as a caught
defect. A lost proof is not a refutation, and a rejection test that cannot tell them
apart is not a rejection test; this was the repo's own "isolate the guard" rule,
violated by the gate that enforces it. The driver now requires `Failed` with the
*expected obligation kind* per fixture — the panic for the swapped `sat_add`, the
postcondition for the wrong-arm `clamp`, the loop invariant for the wrong-body
`sum_to` — and rejects `Skipped`, `Incomplete`, a driver error, a missing function,
or a failure on the wrong obligation.

Both Coq **and** Lean are required. An earlier version skipped whichever was
absent and still reported success, so a machine with only one of them would print
"every claim held" without having checked one of the two proof suites. A missing
prover is now exit `2` (a reported skip) and never exit `0`.

## Reproducing

`discharge` needs a nightly `rustc` for the MIR frontend (the repo pins one).
The other tools are external, and none of them is a dependency of the crate.

```console
# The whole gate, in one command: the discharge driver, Coq and Lean, both
# mutation-checked. Exits 2 (a reported skip) when coqc, lean or a nightly
# rustc is absent, and never 0 for work it did not do.
sh tools/comparison/run.sh

# Or the discharge half on its own -- per-function outcome, not a count
DISCHARGE_RUSTC=$(rustup which --toolchain nightly-2026-08-21 rustc) \
  cargo run -q --features std --example comparison_check

# The raw coverage scoreboard, for the numbers rather than the verdicts
DISCHARGE_RUSTC=$(rustup which --toolchain nightly-2026-08-21 rustc) \
  cargo run -q --features std --example mir_coverage -- examples/comparison/target.rs

# Kani -- copy the harness into a crate with `kani` on the path
cargo kani --version        # 0.68.0
# Verus
verus --crate-type lib examples/comparison/verus.rs
# Prusti 0.2.2 -- needs its pinned nightly-2023-08-15 and a JDK 21
prusti-rustc --edition 2021 --crate-type lib examples/comparison/prusti.rs
# Coq -- each file its own compilation unit; `-Q coq ""` puts model.v on the load path
coqc -Q examples/comparison/coq "" examples/comparison/coq/model.v
coqc -Q examples/comparison/coq "" examples/comparison/coq/example.v
coqc -Q examples/comparison/coq "" examples/comparison/bugs/coq/teeth_sat_add.v
coqc -Q examples/comparison/coq "" examples/comparison/bugs/coq/teeth_sum_to.v
# Lean 4, core only, no Mathlib; the model must be compiled to an .olean first
lean -o examples/comparison/lean/model.olean examples/comparison/lean/model.lean
LEAN_PATH=examples/comparison/lean lean examples/comparison/lean/example.lean
LEAN_PATH=examples/comparison/lean lean examples/comparison/bugs/lean/teeth_sat_add.lean
LEAN_PATH=examples/comparison/lean lean examples/comparison/bugs/lean/teeth_sum_to.lean
# SPARK -- needs `alr install gnatprove`; `obj/` is generated and ignored
gnatprove -P examples/comparison/spark/example.gpr --level=2
gnatprove -P examples/comparison/bugs/spark/example.gpr --level=2
# Ferrocene -- a qualified compiler, not a verifier; absent without a
# customer-portal token, in which case run.sh exits 2 and gate.sh skips it
sh tools/ferrocene/run.sh
```

The Coq and Lean `.vo`/`.olean` outputs are build artifacts and are gitignored
(alongside SPARK's `obj/`), so a run leaves the tree dirty only in ignored
paths.

Tool versions used for the table: `rustc` 1.99.1 (nightly 2026-08-21 for the
MIR frontend), Kani 0.68.0, Verus (2026-08 build), Prusti 0.2.2 (2023-08-22),
Coq 8.20.1, Lean 4.35.0, `gnatprove` FSF 16.1.0.
