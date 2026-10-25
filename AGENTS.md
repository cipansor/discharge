# AGENTS.md

Repository-level notes for agents working in this workspace.

## Layout

- `sparkrs/` — a Rust crate (`sparkrs`) that embeds a formal-verification
  engine: a bit-blasting SMT decision procedure, a symbolic DSL, a
  Curry–Howard proof kernel, contracts, and exhaustive verification.
  `no_std`, zero dependencies, allocation-free.

## Build and test commands

Rust is installed under `~/.cargo`; prepend it to `PATH` in every shell:

```bash
export PATH="$HOME/.cargo/bin:$PATH"
```

```bash
cd sparkrs

# Host build + full test suite (needs the `std` feature for the thread-local arena)
cargo test --features std

# Lint (must stay at zero warnings)
cargo clippy --features std --all-targets

# Docs (must stay at zero warnings)
cargo doc --features std --no-deps

# Bare-metal: no std, no allocator, no dependencies
cargo build --no-default-features                       # host, exercises `static mut` path
cargo build --no-default-features --target thumbv7em-none-eabihf

# The flagship demo
cargo run --features std --example flight_control
```

`clippy` was installed with `rustup component add clippy`; the bare-metal target
with `rustup target add thumbv7em-none-eabihf`.

## The imperative layer (`wp.rs`) has three traps

If you touch verification-condition generation, these are the mistakes that make
it *silently* prove nothing useful:

1. **Walk backwards from the postcondition.** The contract is
   `pre => wp(body, post)`. Starting the walk from `pre` produces a vacuous
   condition.
2. **Do not rewrite loop obligations with the dominating assignments.** Loop
   preservation and exit are quantified over every loop-head state, so they are
   recorded in loop-head terms. Rewriting them makes them trivially true once the
   initialisation pins the variables — a broken invariant passes. Assertions are
   the opposite and *are* rewritten, then wrapped in `pre =>` at the end of
   `verify`.
3. **Termination is a separate obligation.** `While.variant` is optional; with it
   the engine derives the measure after one iteration by *symbolic evaluation*
   (`variant_after`, which builds expressions, not predicates) and emits
   `I && c => V' < V`. Without it, only partial correctness holds and
   `Report::correctness()` says `Partial`. `has_termination_proof()` compares the
   loop count against the variant count: one unannotated loop makes the whole
   report partial.
   A known gap: `variant_after` treats a nested `while` as a no-op, so an outer
   measure must already account for the inner loop.

## The memory layer (`mem.rs`) is a bounded array, not a heap

`Mem` is `2^addr_width` cells, one symbolic word each. `read` at a symbolic address
is an ite chain; `store` is a *simultaneous* update produced by `store_binds` and
applied through `smt::substitute` (or `Stmt::AssignMany`). Two things to keep in
mind when editing:

1. **Address width must match the cell count exactly.** A wider address could name
   a value that is not a cell and would silently alias onto the last one, so
   `check_addr` rejects it. `declare`/`Mem::new` enforce the power-of-two length
   and the `MAX_CELLS` cap.
2. **Old values need capturing.** A postcondition lives in the final state, so
   substitution rewrites every cell variable in it. Writing `m.read(i)` in a
   postcondition means the *new* contents; assign old contents to fresh variables
   first. `tests/mem.rs` shows the swap done correctly.
3. **Prefix predicates come from `quant`, not from the engine.** "All cells below
   k" is a bounded quantifier, and `Mem::forall_below` expands it into one guarded
   conjunct per cell. That is what makes a fill or scan loop verifiable. Two traps:
   the loop counter must be *wider* than the address (a 2-bit counter cannot hold 4),
   so `Mem::addr_of` truncates at the point of use; and the expansion cost is linear
   in the range, so the bound must be a number the tool can count to. Do not add real
   quantifiers to the bit-vector logic — that is a different decision procedure.
4. **`truncate` is the only width-changing operation.** `Op::Trunc` carries its
   source width in the node's `b` field, which means the substitution walker must
   treat it like a shift (carry `b` verbatim) rather than substituting it, and the
   SMT-LIB exporter must render it as `((_ extract w-1 0) x)`. Adding a width-changing
   op without updating those three places will produce silently wrong widths.

## A call is reasoned about through a contract, never through a body

`Stmt::Call` assumes the callee's `ensures` and discharges an obligation to establish
its `requires`. The body is never looked at, which is what makes verification modular
and also what makes the frame check load-bearing:

1. **`ensures` is an assumption, so it must imply the continuation** — `ensures => Q`,
   not `ensures && Q`. Conjoining demands the callee's result satisfy the caller's
   postcondition unaided, which makes every interesting call unprovable. I had this
   wrong first; `a_call_is_reasoned_about_through_the_contract_alone` catches it.
2. **`requires` is an obligation, so it is recorded like an assertion**: dominating
   assignments rewrite it and `verify` wraps it with the precondition. That is why
   `Rule::CallRequires` appears alongside `Rule::Assertion` in both substitution
   sites in `collect` and in `verify`.
3. **A write landing on a variable the call also reads is a soundness hole, not
   tidiness.** With `x -> a, r -> a`, the assumed `ensures` becomes `a == a + a`,
   which forces `a == 0` and lets the engine prove anything. `Stmt::frame` rejects it;
   the caller must capture old values into a temporary, as for a memory swap.
4. **An unmodelled call is reported (`Rule::CallFrame`), never asserted away.** A
   verifier that aborts on bad input cannot be run on a program you do not yet trust.
5. **`frame` checks shape, not meaning.** Renaming a write onto the wrong variable
   passes. Do not try to "fix" this with a smarter check; the fix is `verify_proc` on
   every body, and the limitation is documented where a user will meet it.
6. **The declared frame must be *complete*, checked against `wp::writes(&body)`.**
   `writes` derives the real frame from the syntax and recurses through branches,
   loops and nested calls (mapping a nested callee's writes through that call's
   actuals). Without this a caller could declare an empty frame for a callee that
   clobbers a variable, and the engine would prove the variable survived. That is a
   proof about a program that does not exist, and it is the worst class of bug in a
   verifier. Over-declaring is allowed: the rule is conservative.
7. **A call havocs its written targets: rename each to a fresh variable in both the
   assumed `ensures` and the continuation.** Skipping this makes the pre-call value
   masquerade as the post-call result (`c := 99; c := bump(a)` "proved" `c == 99`).
   The fresh variable is universally quantified, which is the correct reading: the
   caller must hold for every result the contract permits. `variant_after` havocs too,
   so a call that writes the loop measure honestly makes termination unprovable.
8. **Two-state specs use a caller snapshot, not an `old` operator.** For a variable
   the callee cannot write, `old(v)` and `v` coincide, so no operator is needed; the
   missing piece was a *query*, `wp::unchanged`, which answers from the derived frame.
   For a written variable there is no shortcut -- snapshot into a temporary first.
   Do not add an `old` operator to the symbolic layer to "fix" this: it would give a
   name to a value the state no longer contains.

Recursion is deliberately unsupported: a cyclic call graph needs an induction
principle, which is a different feature rather than a missing branch.

## A verifier needs a differential harness, not just unit tests

Both soundness holes in the call rule were found by accident. `tests/modular_differential.rs`
is the deliberate version: generate callers, verify, then *interpret concretely* and
require that a proof never outruns reality. Three rules for keeping it honest:

1. **Validate the oracle before trusting it.** `smt::evaluate` is the concrete semantics
   and the harness's oracle; `the_evaluator_agrees_with_the_engine_on_every_operator`
   pins it against the engine. If you add an `Op` variant, add it to `eval_term` *and*
   to that test, or the oracle silently becomes a second guess.
2. **Seed what the call writes.** A missing havoc rule is invisible unless a written
   variable holds a distinguishable value before the call. The generator assigns `t`
   before calling, precisely so that "the call left `t` alone" is a falsifiable claim.
   Any new soundness rule needs the same treatment: construct the state where breaking
   it is observable.
3. **Show the check can fail.** `the_property_has_teeth` runs one case under a
   deliberately wrong semantics for calls and requires the detection. When adding a
   rule, disable it once and confirm the harness goes red; a green check that has never
   been red is not evidence of anything.

The interpreter is honest about the *declared* frame, so it reproduces the unsoundness
of an under-declared frame rather than hiding it. Do not "fix" that by having the
interpreter consult the body: the point is to model the declared contract, which is what
a real machine executes against.

## The harness must cover every module, or it certifies only the covered ones

The differential harness had three families -- calls, loops-with-calls, obligation pressure
-- and memory had none. Memory is the most algebraic module in the crate (ite-chain read,
simultaneous store bindings, a derived frame lemma, a guarded quantifier), so that gap was
not a coverage statistic; it was the module most likely to hold a silent disagreement with
concrete execution, and the least checked.

The fourth family compares the engine against a concrete array over an enumerated state
space of four 8-bit cells, in *both* directions, because the state space is small and
closed. Two lessons from writing it:

* **A teeth test must break in the dangerous direction.** My first attempt at a deliberately
  wrong store rule made a copy keep the destination's own value, which is the identity: the
  engine honestly said "not proved", so nothing was caught, and the teeth test failed for
  the right reason. Proving *too little* is not a soundness bug. The rule has to prove *too
  much* -- the working version writes `val` to every cell and ignores the address, which
  makes `m[1] == 5` provable after `m[0] := 5`.
* **Assert non-vacuity explicitly.** A generated family can pass by producing no interesting
  cases. Both counts are asserted: at least one case proved, at least one refuted.

The teeth check that matters is against the *real* rule: break `store_binds` so it ignores
the address, and the family reports `VERIFIED but 4320 sampled (array, address) pairs
violate`. That is the harness doing its job on the code it exists to guard.

Also, twice now a heredoc-written patch has corrupted a file (a stray leading byte spliced
into the first line). Prefer the editor tool for multi-line Rust; keep heredocs for shell.

## The recurring class: a limit that truncates instead of reporting

Five soundness holes in a row, all the same shape — a bounded buffer or a width that
silently truncates a value, so a summary outruns the evidence behind it:

| Claim | Evidence lost | How |
|---|---|---|
| `verified` | callee body | under-declared frame |
| `Total` | variant verdict | counted instead of discharged |
| `verified` + `Total` | obligations | dropped at `MAX_OBLIGATIONS` |
| `verified` + queries | real frame | truncated at `MAX_WRITES` |
| `Valid` from `exists_guarded` | index range | index truncated to the bound's width |

Two of these were *not* buffer caps but width truncations of a value, which is the same
failure in different clothing: `word(k, w)` silently keeps only the low bits of `k`. When a
value is narrowed for a comparison, ask whether the comparison is still the one intended.

When auditing, the questions that found all five:

1. Where does a count stop early, and does anything downstream know it stopped?
2. Where is a value narrowed, and can narrowing change a comparison's answer?
3. Which summaries (`verified`, `Total`, `Valid`, `unchanged`) are computed from partial
   evidence, and what happens when the evidence is incomplete?

Report, never truncate. If a function can return partial data, the partiality belongs in
its type.

## A truncated set must not look like a small set

Fourth instance of the same class, and the one that defeated the fix for the first.
`writes` derived a procedure's real frame into a `MAX_WRITES` buffer and returned
`(array, count)`, truncating silently. The frame-completeness check added for the
under-declared-frame hole then compared the declared frame against a *prefix* of the truth,
so a callee writing more than `MAX_WRITES` variables was indistinguishable from one writing
exactly that many — and a caller could prove a clobbered variable survived the call.

The fix is a type change, not a flag: `writes` returns `Frame`, whose `complete()` is
`false` past the cap, and `Stmt::frame`, `unchanged_vars` and `unchanged` all treat an
incomplete frame as an unmodelled program. A separate boolean return value would have been
easy to ignore, which is exactly what happened for three rounds.

Two lessons worth keeping:

* **A count that saturates is not a count.** `(buf, n)` where `n` stops at the cap carries
  no information about whether it stopped. If a function can return partial data, the
  partiality has to be part of its type or it will be lost at some call site.
* **Independent constants that must stay in a relation are a bug waiting.** `MAX_WRITES`
  and `MAX_CALL_ARGS` had to satisfy `MAX_WRITES <= MAX_CALL_ARGS` for `unchanged_vars` to
  be total, and nothing said so. It is now a `const _: () = assert!(..)`.

Also: when a heredoc-written Python patch garbles itself, the failure mode is duplicated
definitions, not a clean error — `git checkout` the file and use a precise edit instead.

## A capped summary must fail loudly

`MAX_OBLIGATIONS` is a fixed-size buffer, and `push` used to drop obligations silently when
it filled. A program with more side obligations than the cap could therefore report
`verified` — and `Total` — while a failing `LoopExit` sat in the part that did not fit. Two
rules follow, and both bit me:

1. **Claim-carrying obligations must report the drop.** Loop rules and call rules go
   through `push_checked`, which raises an `ObligationOverflow` obligation with goal
   `false`. Assertions may still be dropped quietly, because a dropped assertion poisons
   the weakest precondition and the contract obligation catches it.
2. **The notice needs a slot the program cannot occupy.** `Report::obligations` is one
   longer than `MAX_OBLIGATIONS`, and `push` stops at `program_limit` (one below the end)
   while `push_notice` may use the last slot. My first fix appended the overflow obligation
   with `push`, so a full buffer dropped the notice too and the report still said
   `verified`. When adding a report-level finding, reserve its space explicitly.

The general lesson, which is the third instance of the same class: **a summary claim is
only as good as the checks behind it.** `verified`, `Total` and `Partial` are summaries.
Whenever one is computed, ask what happens when the underlying evidence is incomplete —
missing, dropped, or merely assumed — and make that case a failure rather than a silence.

## Termination claims must be discharged, not counted

`Report::has_termination_proof` counts only variant obligations whose verdict is
*proved*. Counting the obligations instead of discharging them was a real defect: a
loop whose measure does not decrease reported `Total` while the report was unverified.
When adding a rule that contributes to a summary claim, discharge the obligation before
letting it count. `Report::establishes` answers "verified?" and "termination proved?"
together, so a caller cannot read the optimistic half alone.

## A behavioural harness cannot see a proof defect

Worth knowing before trusting the differential harness too far. The termination defect
above is invisible to concrete execution: a loop with a non-decreasing variant still
*terminates*, so `verified => no violating execution` says nothing about it. What made
it visible was a loop that diverges *and* is claimed total — the divergence is behaviour,
the claim is proof, and the two only meet when the proof is wrong in the direction that
lets a divergence through.

Two consequences for the harness:

1. Check a summary claim **outside** the `verified` branch. A claim like `Total` matters
   most when the report failed, and that is exactly when an assertion nested inside
   `if verified` never runs. My first version of the loop check had this bug and so
   missed the defect entirely.
2. Read the claim the way a careless caller would. The harness deliberately reads
   `correctness()` rather than `establishes()`, because `establishes()` folds a failure
   into `Nothing` and would hide the defect. Test the sharp edge, not the safe wrapper.

## Architecture (read this before editing `smt.rs`)

`src/smt.rs` is the heart: bit-vector terms are bit-blasted into a Reduced
Ordered BDD. Invariants that are easy to break and hard to debug:

1. **Terminal nodes must have `var == u32::MAX`.** `top_var`/`cofactors` use that
   to mean "no variable here". `ensure_ready()` sets this. If it is wrong you get
   a non-canonical diagram and exponential blow-up, *not* an error.
2. **Every recursive cache must be cleared by `reset()`.** `reset()` clears
   `and_*`, `or_*`, `xor_*`, `not_*`, `uniq_*` and `term_*` in place (it must not
   use `*self = Ctx::new()`, which materialises a large stack temporary). Forgetting
   a cache leaves stale node ids pointing at recycled nodes, which produces a
   cycle and an infinite recursion (stack overflow).
3. **`neg()` must stay memoised.** Without the cache it walks shared subgraphs
   once per path, which is exponential; a few thousand nodes then takes minutes.
4. **Comparison ops (`Eq`/`Ult`/`Ule`) store the *operand* width**, not width 1.
   `blast` walks all operand bits and writes `out[0]`. Storing width 1 makes every
   comparison look at bit 0 only.
5. **BDD variable order** is `level_of` = interleaved bit-planes. This keeps
   adders/comparators linear. Changing it will silently make proofs slow or
   return `Unknown`.
6. **The substitution epoch must be bumped, never reset.** `reset()` and
   `clear_subst()` call `bump_epoch()`. Restoring an earlier epoch makes stale
   `subst_memo` stamps look current, and the memo then returns node ids that
   `reset` has already recycled: a cycle in the term graph and unbounded
   recursion. This was a real bug, not a hypothetical.
7. **`with_fresh` must not be nested.** The inner call wipes the arena while the
   outer scope still holds live `Var`s. The symptom is unbounded recursion, not a
   clean panic.

## Conventions

- `Verdict::Unknown` is a first-class, correct answer when the node budget is
  exhausted. Never "fix" a proof by making the engine guess; either raise `CAP`
  or state a smaller-width obligation.
- Proofs that fail are usually mis-stated, not engine bugs. Verify a surprising
  result by hand (or with `exhaustive`) before touching the engine.
- The differential test (`tests/differential.rs`) is the trust anchor: symbolic
  proof and brute-force execution must agree, and symbolic counterexamples must
  be real.
- Keep the README honest about limits. Do not claim memory/aliasing/concurrency
  coverage; the logic is bit-vectors and booleans only.
