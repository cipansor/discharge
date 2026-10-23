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

Recursion is deliberately unsupported: a cyclic call graph needs an induction
principle, which is a different feature rather than a missing branch.

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
