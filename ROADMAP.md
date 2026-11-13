# Roadmap

The single place open work lives. `AGENTS.md` records what was *learned*; this
file records what is *left*, in the order it blocks ordinary Rust. Every item has
five fields, so "is this done?" is a check rather than an opinion:

- **Priority** — P0 (blocks everyday code), P1 (needed to verify a real crate),
  P2 (parity with the high end).
- **Exit criterion** — a command whose output decides the item.
- **Competitor** — the tool whose gap the item closes.
- **Move** — **build** it, **bridge** to a tool that has it, or **won't do**.
- **Status** — done / in progress / todo / won't do.

A PR that closes an item updates its status here in the same PR.

The starting numbers, measured on the branch that created this file, are the
baseline every item is scored against:

| Corpus | Command | Verified / decided |
|---|---|---|
| `examples/mir_targets/actuator.rs` | `cargo run --features std --example mir_coverage -- examples/mir_targets/actuator.rs` | 15 / 30 |
| `examples/mir_targets/realistic.rs` | same, `realistic.rs` | 398 / 737 |
| `examples/mir_targets/everyday.rs` | same, `everyday.rs` | **9 / 21 (43%)** |

`everyday.rs` is the honest one: ordinary Rust written by an external reviewer,
not shaped for the tool. `realistic.rs` is a regression corpus (about a third of
it is adversarial fixtures), so its high percentage does not measure coverage of
ordinary code. Phase 1 is defined on `everyday.rs`.

---

## Phase 1 — everyday Rust (P0)

Exit: `everyday.rs` at least **80% decided** (17 of 21), and four weeks in a row
with no new false proof while the independent corpus keeps growing.

### The Rust edition (E items)

- **E1. Use the crate's own edition.** · P0 · done · Kani (whole-crate builds)
  - Gap: the frontend pinned `--edition=2024`, so a valid 2021 crate
    (`extern "C" { … }` must be `unsafe` from 2024) was refused, and code that
    lowers differently from the edition that ships could be verified as a program
    nobody built.
  - Exit: a 2021 `extern "C"` fixture produces MIR and verifies. ✅
  - Move: **build** (read `package.edition` from the nearest `Cargo.toml`,
    resolving `edition.workspace = true`). See `resolve_edition`.
- **E2. An explicit override, and no silent default.** · P0 · done · —
  - Exit: `MirOptions { edition }` and `VERIF_EDITION` override it; a loose file
    with neither is an error naming the missing edition. ✅
- **E3. Stamp the edition on every result.** · P0 · done · —
  - Exit: `FileReport.edition` is recorded and `mir_coverage` prints it. ✅
- **E4. An edition matrix in the gate.** · P1 · todo · Kani
  - Gap: nothing runs the corpus under 2015/2018/2021/2024 and requires identical
    verdicts, and no fixture pins the per-edition lowering differences
    (`begin_panic` vs `panic_fmt`, `if let` rescoping, tail-expression
    temporaries, the never-type fallback).
  - Exit: `scripts/gate.sh` runs `actuator.rs` under all four editions with the
    same verdicts, plus one fixture per lowering difference.
  - Move: **build**.
- **E5. One source for the edition.** · P1 · done · —
  - Exit: `tools/mir-oracle` takes the edition from the frontend's resolver
    (`emit_mir_opts` returns it) rather than repeating a literal. ✅
- **E6. The misleading hint.** · P0 · done · —
  - Exit: `mir_coverage` prints the frontend's error (which names the compiler, the
    edition and the reason) instead of "set VERIF_RUSTC to a nightly". ✅

### Coverage (C items)

- **C1. `Drop` and cleanup edges.** · P0 · in progress · Kani, Prusti, Creusot,
  Verus, SPARK
  - Gap: `drop(_x) -> [return: bbN, unwind …]` is unmodelled, so any function with
    an RAII local (`Vec`, `String`, `Box`, a lock guard, a user `Drop`) is
    incomplete.
  - **C1b (done):** a diverging call in its *cleanup* form
    (`_4 = core::panicking::panic(…) -> bb4`, `bb4 (cleanup)`) was not recognised,
    so an `assert!` in any function with a live `Drop` local was a dropped path.
    Now read as a diverging call: `guard_misguarded` FAILED with a counterexample
    (`x = 224`). ✅
  - Remaining: model `drop` itself (a no-op for a type with no drop glue; a call
    through the call machinery for a user `impl Drop`; a no-op for std containers,
    which change no scalar state).
  - Exit: `guard_guarded` verified (today: incomplete on the unmodelled `drop`).
  - Move: **build**.
- **C2. `Option`/`Result` and `?`.** · P0 · todo · Kani, Verus, Prusti, Creusot
  - Gap: `unwrap`, `unwrap_or`, `expect`, `ok_or`, `map`, `is_some` and `?` are
    unmodelled. Evidence: `checked_or_max`, `div_unwrap` incomplete.
  - Approach: the enum payload/discriminant model exists; add a **contract library
    for std/core** in the spirit of Prusti `#[extern_spec]` / Verus `vstd`, each
    spec differential-tested against the real implementation.
  - Exit: `checked_or_max` and `div_unwrap` verified; a misused `unwrap` refuted
    with a counterexample.
  - Move: **build**.
- **C3. Ranges and `for` loops.** · P0 · todo · Kani, Verus, Prusti
  - Gap: `RangeInclusive::new`, `Range`, `Iterator::next` unmodelled, so the
    commonest loop in Rust is out of reach. Evidence: `tri` incomplete.
  - Approach: model `Range`/`RangeInclusive` as structs, `next` as a modelled
    intrinsic, recognise the `for` desugaring, reuse the loop machinery.
  - Exit: `tri` verified with an `invariant:`; a missing invariant reported as *a
    missing invariant*, not "unmodelled".
  - Move: **build**.
- **C4. Loops without path explosion.** · P0 · in progress · Kani (unwinding),
  Verus, Creusot, Prusti, SPARK (`Loop_Invariant`/`Loop_Variant`), Flux
  - Gap: a 4-iteration loop over an array exhausts the 64-path budget. Evidence:
    `max_of` incomplete (`path budget exhausted after 64 paths`).
  - (a) `invariant:`/`variant:` clauses inside the MIR frontend — **partly
    built** (the `Cut` machinery and the loop obligations exist; `everyday.rs`
    needs a fixture that uses them). (b) a bounded-unrolling mode whose bound is
    *reported*, so a too-small bound fails rather than silently cutting paths.
    (c) merge states at joins (ite-merging) instead of enumerating paths.
  - Exit: `max_of` verified with an invariant and with `unwind: 5`, refuted with
    `unwind: 3` by the unwinding check.
  - Move: **build**.
- **C5. Enums with payloads and match guards.** · P0 · in progress · Kani
  - Gap: `match m { Run(n) if n < 10 => … }` gives "unmodelled switch
    discriminant". Evidence: `next_mode` incomplete.
  - Exit: `next_mode` decided, plus one refuted fixture.
  - Move: **build** (the payload/discriminant model exists; the guard on a
    `switchInt` arm is the missing piece).
- **C6. The everyday `core` surface.** · P0 · in progress · Kani, Verus (`vstd`)
  - Gap: `Ord::min/max/clamp`, `iN::abs`, `abs_diff`, `rotate_*`, `is_ascii_*`,
    `<[T]>::len/is_empty/first/get`. Evidence: `abs_small`, `clamp_builtin`,
    `digit`, `first_or` incomplete. `min`/`max` and `From`/`Into` are already
    modelled; the rest are not.
  - Approach: the C2 contract library, plus a published list of the modelled
    `core` items with each item's oracle.
  - Exit: `abs_small`, `clamp_builtin`, `digit`, `first_or` verified; the list is
    in the docs.
  - Move: **build**.
- **C7. Arithmetic scale and speed.** · P0 · in progress · Kani, Boolector,
  Bitwuzla
  - Gap: `u32::wrapping_mul` is past the 32-bit model; `clamp_std` takes 9.9 s.
    Evidence: `hash_step` incomplete; `clamp_std` verified in 9.89 s.
  - Approach: word-level preprocessing before bit-blasting (rewriting, constant
    propagation, lazy multiplication abstraction), a better SAT encoding for
    multipliers, and a per-function **time** budget beside the size budget so a
    slow shape is reported rather than waited out.
  - Exit: `hash_step` decided; `clamp_std` under 0.5 s.
  - Move: **build**.

### Trust tracking (A1, tracked from Phase 1)

- **A1. Track the false-proof rate.** · P0 · in progress · —
  - Data: at least 11 false proofs were fixed between 2025-11-04 and 2025-11-12.
    All were caught, but at that rate a `verified` is not yet evidence to rely on.
  - Approach: a `SOUNDNESS.md` listing every false proof with date, commit,
    root-cause class and fixture. Pause feature work on any layer that produced a
    false proof in the last two weeks.
  - Exit for "beta": four weeks in a row with no new false proof, while the
    independent corpus keeps growing.
  - Move: **build**. (`AGENTS.md` is the raw material; the extraction is todo.)

---

## Phase 2 — real crates (P1)

Exit: one real `no_std` crate with a dependency verified end to end with
`cargo verif`; Kani agrees on every function both tools decide.

- **C8. Cargo, multi-module crates and dependencies.** · P1 · todo · Kani
  (`cargo kani`)
  - Gap: the frontend runs `rustc --crate-type=lib` on one file, without
    `--extern`, so a crate that `use`s another crate, or a file whose
    crate-relative paths only resolve inside the crate, cannot be verified.
  - Approach: a `cargo verif` subcommand through `cargo rustc`/`RUSTC_WRAPPER`,
    emitting MIR for the target crate with its real flags. Dependency calls are
    answered through contracts (C2), not bodies.
  - Exit: one function in a real `no_std` crate with at least one dependency
    (an `embedded-hal` driver, say) verified end to end with `cargo verif`.
  - Move: **build**.
- **C9. References and aliasing.** · P1 · in progress · Prusti (ownership),
    Creusot (prophecies)
  - Gap: reference arguments are refused ("no aliasing model"), yet `&`/`&mut`
    are the norm. **Partly built:** `&T`/`&mut T` arguments, writes through them,
    returned references and two-reference targets are modelled (see the `AGENTS.md`
    sections on the call boundary). What remains is the *general* case the
    ownership model buys.
  - Exit: `fn bump(c: &mut u16)` with `ensures: *c == old(*c) + 1` verified and
    its caller verified modularly.
  - Move: **build**.
- **C10. Generics, traits, closures and `dyn`.** · P1 · in progress · Kani
  (monomorphised instances)
  - Gap: generics are partly supported; "indirect call not modelled" ends the
    path; closures are out of reach. Trait-method identity and contract
    inheritance have started.
  - Exit: a closure-taking function (`v.iter().map(|x| …).sum()`) decided for a
    monomorphised instance.
  - Move: **build**.
- **C11. Heap containers.** · P1 · todo · Kani, Verus (`Seq`), Creusot
  - Gap: `Vec`, `String`, `Box`, symbolic-length slices. Evidence: `make`
    incomplete.
  - Approach: a bounded *sequence* model (length plus element array, from `mem`),
    exposed through contracts for `Vec::{new, push, pop, len, get, index}`.
  - Exit: `make` verified.
  - Move: **build**.
- **C12. A specification language that can say more.** · P1 · in progress · Verus,
  Creusot, Prusti, SPARK
  - `old(x)` in contracts; quantifiers; mathematical integers (a spec must not
    overflow itself); pure spec functions; ghost code and lemmas; `modifies`/frame
    clauses; type invariants. **Partly built:** `old` via a caller snapshot and a
    `wp::unchanged` query, bounded quantifiers in `quant`, frames derived by
    `wp::writes`.
  - Exit: a contract with a `forall i < n: a[i] <= m` verified.
  - Move: **build**.
- **C13. Rust's own contract attributes as input.** · P1 · todo · the `contracts`
    crate
  - Approach: read `#[core::contracts::requires/ensures]`
    (rust-lang/rust#128044) as well as doc comments, keeping doc comments as the
    stable fallback.
  - Exit: a function carrying the attribute instead of a doc comment is verified.
  - Move: **build**. Without it, a home-grown syntax risks being absorbed by the
    language's own — the risk the README already names.

### Usability (U items, Phase 2 subset)

- **U1. Publish to crates.io, or stop saying `cargo add verif`.** · P1 · in
  progress · —
  - Gap: the README's Installation section says `cargo add verif`, but the crates
    are not on crates.io (the API answers "does not exist"). The packaging work is
    done (`scripts/publish.py`, `scripts/check_package.sh`, a tag-driven
    `.github/workflows/release.yml`), so what remains is the human step: create the
    `CARGO_REGISTRY_TOKEN` secret and push a `verif-arithmetic-v0.1.0` tag, then
    `verif-v0.1.0`. Until then, either publish or change Installation to a git
    dependency.
  - Exit: `cargo add verif` works, or the README points at a git dependency.
  - Move: **build**.
- **U2. `cargo verif`.** · P1 · todo · Kani (`cargo kani`)
  - Exit: `cargo verif --format json|sarif` plus a GitHub Action that annotates a
    PR.
  - Move: **build**.
- **U3. A counterexample becomes a test.** · P1 · in progress · Kani (concrete
    playback)
  - Gap: the replay machinery exists in `tests/mir.rs`; make it a user feature
    that emits a `#[test]`.
  - Exit: a reported counterexample is emitted as a compiling, failing-then-fixed
    `#[test]`.
  - Move: **build**.
- **U4. Readable counterexamples.** · P1 · in progress · —
  - Gap: a report says `v1:u8 = 224`, not `x = 224`. The `debug x => _1` names
    exist; the stable text dump has no per-statement spans, so line numbers come
    from the source scanner or the `rustc_public` path.
  - Exit: `x = 224` in a report.
  - Move: **build**.
- **U5. A test harness that never passes vacuously.** · P1 · in progress · —
  - Gap: about 21 tests in `tests/mir.rs` use
    `let Some(report) = verify_all() else { return }`, so without `VERIF_RUSTC`
    they *pass while checking nothing* (a skipped test reports `ok`). `gate.sh`
    step 8 and CI now fall back to `rustc` on `PATH`, and `verify_src` is strict
    (a dropped contracted function panics), but the `else { return }` shape is
    still silent on a machine with no `rustc` at all.
  - Exit: every such test either runs (a `rustc` is found) or is
    `#[ignore = "needs a rustc"]`, so the count with and without the toolchain
    differs only by the ignored ones.
  - Move: **build**.
- **U6. Documentation size.** · P1 · todo · —
  - Gap: the README is ~166 KB and `AGENTS.md` ~586 KB. Split into a short README,
    a user guide, `ROADMAP.md` (this file), `SOUNDNESS.md`, and design notes.
  - Exit: a README under ~30 KB with links to the rest.
  - Move: **build**.
- **U7. Proof caching.** · P1 · todo · —
  - Exit: unchanged MIR plus unchanged contracts reuses the verdict across runs.
  - Move: **build**.
- **U8. A public scoreboard.** · P1 · todo · Kani
  - Exit: `everyday.rs`, an SV-COMP-style set, and `verify-rust-std` functions
    scored for verif **and** Kani on the same inputs, updated by CI.
  - Move: **build**.

---

## Phase 3 — trust (P0 for adoption)

Exit: every `Unsat` behind a `verified` carries a checked certificate; the public
scoreboard against Kani is live.

- **A2. A certificate for every `Unsat`.** · P0 · todo · Kani, Verus, Prusti,
    Creusot (all trust their solver)
  - Approach: emit LRAT/DRAT from the CDCL solver and check it with an independent
    checker (`drat-trim`, ideally the verified `cake_lpr`); in CI re-derive BDD
    verdicts through the certifying SAT path.
  - Exit: a `verified` verdict whose SAT certificate is re-checked by an external
    tool.
  - Move: **build**. This is a way to be *ahead* of the competition on trust, not
    just catch up.
- **A3. Re-check selected obligations in Coq or Lean.** · P1 · todo · Coq/Rocq,
    Lean
  - Approach: `examples/comparison` already has Coq and Lean files; make "export
    this obligation as a Lean/Coq goal" a user-facing option.
  - Exit: one obligation from `everyday.rs` re-checked by a kernel.
  - Move: **bridge**.
- **A4. A trusted computing base and a semantics.** · P1 · todo · —
  - Write down what is trusted (parser, MIR-printer stability, executor, blasters,
    solvers), a short formal semantics of the supported MIR subset, and back both
    with mutation testing (exists) and external review before any 1.0 claim.
  - Exit: a `SECURITY.md`-style TCB document and an external review.
  - Move: **build**.
- **A5. A qualification path.** · P2 · todo · SPARK (the only one with
    qualification kits)
  - Approach: draft Tool Operational Requirements and a DO-330 TQL-5 / ISO 26262
    TCL plan. Together with Ferrocene, this is the most credible embedded-safety
    differentiator.
  - Exit: a drafted TOR and qualification plan.
  - Move: **build** (long term).
- **A6. Kani as a standing oracle for the frontend.** · P1 · todo · Kani
  - Approach: run Kani on every function in `everyday.rs` and `realistic.rs` in
    CI and require agreement whenever both decide. The engine already has Kani and
    Verus oracles; extend to whole-function verdicts.
  - Exit: a CI job that fails on any disagreement.
  - Move: **build**.

---

## Phase 4 — the high end (P2)

Exit: float and ISR fixtures verified; TOR and a qualification plan drafted.

- **C14. Floating point.** · P2 · todo · Kani, SPARK
  - Approach: bit-blast IEEE-754 `+ - * / < ==` with round-to-nearest-even; check
    exhaustively on a small format first. Freedom from NaN/Inf becomes an
    obligation. Matters because the flagship example is *flight control*.
  - Exit: an `f32` fixture verified.
  - Move: **build**.
- **C15. Unbounded proofs.** · P2 · todo · Verus, Creusot, Coq
  - Approach: **pick one and write it here.** (a) a small embedded SMT core with
    linear integer arithmetic, arrays and uninterpreted functions, or (b) a
    **bridge** that sends the obligation to Z3/CVC5 (the SMT-LIB export exists) or
    to Lean/Coq as an optional host-side path.
  - Exit: a "for all n" obligation decided.
  - Move: **bridge** (b) is the honest choice for a bit-blasting engine; (a) is a
    research project.
- **C16. `unsafe` and raw pointers.** · P2 · todo · Kani, VeriFast, RefinedRust,
    Verus
  - Target: *bounded* reads and writes through raw pointers within one allocation,
    plus obligations that a contracted `unsafe fn`'s preconditions hold at each
    call site.
  - Exit: a bounded raw-pointer fixture verified.
  - Move: **build** (the bounded subset only; **won't do** the separation-logic
    general case).
- **C17. Concurrency and interrupts.** · P2 · todo · SPARK (Ravenscar/Jorvik),
    Verus
  - Target: for the `no_std`/MCU story, the *interrupt handler* with shared state
    behind `critical_section` or atomics, not threads. Start with "a
    read-modify-write on an `Atomic*` preserves invariant I when interleaved at ISR
    boundaries", for a bounded number of interleavings.
  - Exit: an ISR fixture verified.
  - Move: **build**.
- **C18. Flow analysis (SPARK's other half).** · P2 · todo · SPARK
  - Gap: `gnatprove` checks data/information flow (`Global`, `Depends`,
    initialisation) before any proof. `rustc` covers initialisation; `Depends`
    does not exist in Rust.
  - Approach: cheap on top of symbolic execution — check that an input the contract
    declares independent does not appear in the support of the output term.
  - Exit: a `Depends`-style contract checked.
  - Move: **build**.

---

## Won't do

Stated plainly so the boundary is a decision rather than an omission. These are
reproducible inside verif only by becoming a different tool.

- **Arbitrary mathematics and induction (Coq/Lean parity).** Bit-blasting cannot
  reach it. **Bridge** through A3/C15b instead.
- **A general separation-logic heap model (`unsafe` at large).** VeriFast and
  RefinedRust do it; verif's bounded `unsafe` subset (C16) is the target.
- **Thread concurrency as a general problem.** The embedded shape (C17) is the
  one that matters for a `no_std` verifier.
- **Qualification *evidence* without a plan.** A5 drafts the plan; shipping the
  evidence is a multi-year activity and is not claimed.

---

## Where this comes from

The items and their exit criteria are the review on PR #8
(`analisaperlengkapan`, 2026-11-13): editions (§2, E items), coverage in priority
order (§3, C items), trust (§4, A items), usability (§5, U items), the per-competitor
gap table (§6), and the phased exit criteria (§7). The comparison to Kani, Verus,
Prusti, Creusot, Coq/Rocq, Lean, SPARK, Flux, VeriFast/RefinedRust/ESBMC and the
`contracts` crate is in §6 of that review and is summarised in the **Competitor**
field of each item.
