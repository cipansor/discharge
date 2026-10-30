# AGENTS.md

Repository-level notes for agents working in this workspace.

## Layout

- The repository root *is* the `discharge` crate: a Rust crate that embeds a
  formal-verification engine — a bit-blasting SMT decision procedure, a symbolic
  DSL, a Curry–Howard proof kernel, contracts, and exhaustive verification.
  `no_std`, zero dependencies, allocation-free. (`src/`, `tests/`, `examples/`,
  `scripts/`, `Cargo.toml` all live at the root.)

## Build and test commands

Rust is installed under `~/.cargo`; prepend it to `PATH` in every shell:

```bash
export PATH="$HOME/.cargo/bin:$PATH"
```

```bash
# Run from the repository root.

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

# The MIR frontend: verify real Rust, reading the MIR rustc lowers it to.
# `--emit=mir` needs nightly, and the compiler is named separately from RUSTC
# so that pointing this at a nightly does not disturb the cargo building it.
DISCHARGE_RUSTC="$(rustup which --toolchain nightly rustc)" \
  cargo run --features std --example mir_demo
DISCHARGE_RUSTC="$(rustup which --toolchain nightly rustc)" \
  cargo test --features std --test mir
```

`clippy` was installed with `rustup component add clippy`; the bare-metal target
with `rustup target add thumbv7em-none-eabihf`.

```bash
# The qualified-toolchain gate, in isolation. Exits 0 on a build, 1 on a real
# failure, 2 when no Ferrocene toolchain is present (which `gate.sh` reports and
# skips). See `tools/ferrocene/README.md`.
FERROCENE_RUSTC=/path/to/ferrocene/bin/rustc sh tools/ferrocene/run.sh
```

## Verifying real Rust: the MIR frontend (`src/mir/`)

The rest of the crate proves things about *models*: a formula, or a `wp` program.
`src/mir/` proves things about the code itself, by reading the MIR that `rustc`
lowers it to. Five facts about it cost the most time to discover:

1. **A MIR dump carries no attributes and no doc comments.** So contracts cannot
   come from MIR; they are scanned out of the *source* text, while bodies come
   from MIR. That split is the design, not a limitation to work around.
2. **`rustc` prints the failing polarity of its arithmetic asserts:**
   `assert(!move (_5.1: bool), "attempt to compute ...")`. Dropping the `!`
   inverts every overflow, underflow and divide-by-zero check, and the tool then
   reports safe code as broken. The flag is carried through the IR and pinned by
   a parser unit test.
3. **A checked binary writes a tuple, and the tuple has no width.** `_3 =
   AddWithOverflow(a, b)` makes `_3` a `(uN, bool)`. Reading the operand width
   from `_3` gives 64 for every type, which silently mis-sizes the overflow test.
   The width comes from `_3.0`.
4. **`smt::truncate` zero-extends when the target is wider.** That is what makes
   the multiplication-overflow predicate exact: compute at `2w`, test the top
   `w` bits against zero.
5. **The output path matters.** `-o /dev/stdout` makes rustc try to create a temp
   directory in `/dev` and fail; the MIR goes to a unique temp file. The name must
   be unique per *call*, not per process, or parallel tests delete each other's
   files.

Three engine consequences worth remembering:

- **Division is now in the engine** (`smt::divmod`, exact, restoring), because a
  frontend reading real code meets `a / b` and must not guess. `y == 0` is a
  *defined* value rather than a hole, and rustc's own divide-by-zero assert is
  what reports the panic. The 1-bit fast path must honour the same `y == 0`
  contract or it disagrees with the general path at exactly that input — a test
  caught this.
- **A variable shift is a barrel shifter** (`smt::shift_var`), `log2(w)`
  conditional stages. It is linear in the width, so it fits where a `w`-bit
  multiplier does not. An out-of-range amount has a defined value (zero, or sign
  fill for an arithmetic right shift), matching the shift-count-masking choice the
  differential oracle already pins.
- **Widened products past 16 bits are declined, not approximated.** `sat_mul` at
  `u16` needs a 32-bit product, which is the BDD wall. A *weaker* overflow
  predicate would be worse than declining, because it would make an overflowing
  function look panic-free. So the code returns "no predicate" and the path is
  reported `incomplete`.
  This was measured rather than assumed. The engine does have a SAT fallback for
  when the arena fills, so the tempting fix is to raise the width and let the
  fallback take it. Raising the threshold from 16 to 32 does not reach the
  fallback: `mir_demo` on `sat_mul` then runs past 300 s and has to be killed,
  because the cost is in *building* the 32-bit diagram, before the arena ever
  fills. The threshold is a time guard, and 16 is where it sits. If you raise it,
  time the demo rather than trusting the fallback's existence.

- **Signedness is part of the *value*, not a display detail.** The engine's
  arithmetic is bit-vector arithmetic, so every operation has one bit-pattern
  answer; signedness decides which *question* a comparison asks. `-1 < 1` is
  `false` read unsigned and `true` read signed, `-7 / 2` is `-3` signed and a huge
  positive number unsigned, and a signed add's overflow is not the unsigned
  carry. The frontend therefore reads signedness off the declared type and picks
  `smt::slt`/`sle`/`sgt`/`sge` and `smt::sdiv`/`srem` rather than the unsigned
  forms. The contract evaluator does the same, because a contract's `<` is the
  same comparison as the code's. Two consequences worth remembering:
  - `MIN` is *not* zero. `parse_const` used to return `0` for both `MIN` and
    `MAX`, so `a != i8::MIN` meant `a != 0` and a signed negation guarded by it
    was reported panic-free. `MIN` of a signed type is the top bit alone.
  - The overflow rules are not the unsigned ones. For a signed add it is "the
    operands agree in sign and the result disagrees"; for a subtract, "the
    operands differ and the result takes the subtrahend's sign". The unsigned
    carry test happens to fire on `127 + 1` but also fires on `-1 + 1`, which is
    not an overflow. For a signed multiply the test is rustc's own: the
    sign-extended product equals the sign-extension of the wrapped result.
    `smt::sign_extend` exists for exactly this, because `truncate` zero-fills and
    a zero-extended `-1` has the wrong magnitude.

Three traps that cost time here, all in the frontend rather than the engine:

- **`Term::Assert` must assume the guard it just checked on the fall-through
  path.** It used to push the success block with the incoming path unchanged, so
  `assert(n < 16)` was proved and then *discarded*: later obligations were
  discharged as if `n` could still be 16. That is sound — the guard is checked
  separately, so no panic is hidden — but it is needlessly weak, and wrong for a
  guard the *caller* wrote. Carrying `satisfied` is what lets `sat_shift` verify.
  If a function that clearly cannot panic comes back `failed` or `incomplete`,
  check whether an assert guard was assumed before blaming the engine.
- **The parser must check ` as ` before `const `.** rustc prints a cast constant
  as `const 3_i32 as u32 (IntToInt)`; matching the `const ` prefix first hands the
  whole string to `parse_const`, which reads `i32 as u32 (IntToInt)` as a type
  name and yields a constant with *no width*. Every guard written against such a
  constant then goes unmodelled. This is why even `x << 3` used to be `incomplete`.
- **The cast's target width is the destination's, not the source's.** `Rvalue::Cast`
  takes the width from the `as T` type; the operand keeps its own width. A shift
  amount is a `u32` even for a `u16` shift, and rustc keeps it distinct, so the
  width used to build the shift is the *left* operand's.

`tests/mir.rs` is the oracle that matters: it feeds each reported counterexample
back into the *compiled* function and requires the panic. That checks the engine
against rustc's code generator rather than against another model. `tests/divmod.rs`
does the same for the divider, against Rust's own `/` and `%`; `tests/shift.rs`
does it for the barrel shifter, against Rust's own `<<` and `>>`.

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

## A total function can still be wrong

Two bugs in `Fixed` (Q16.16) were invisible to the proof layer, because both operations are
total and the engine proves things about them happily.

1. **`to_int` floored instead of truncating.** The doc said "truncated toward zero"; `>> 16`
   is an arithmetic shift, which floors, so `-0.5` gave `-1`. Every negative fractional
   input was off by one. This is the mirror of the shift-amount bug: the operator is total,
   so nothing complains, and the comment described the *intent* rather than the code.

2. **`from_int` wrapped.** Q16.16 in `i32` spans `[-32768, 32767]` integers, and `v << 16`
   silently wraps outside that, so `from_int(32768)` produced `-32768`. Saturating is the fix,
   and it matches what `saturating_add`/`saturating_mul_int` already promise.

The lesson generalises: "this operation cannot panic" is not "this operation is correct". A
primitive that is total by construction (a shift, a cast, a bitwise op) is exactly where a
wrong result hides, because there is no trap to notice. Test the *value*, against the
language's own operator where one exists (`bits / 65536` is the definition of toward-zero).

## Fuzz the layers, not just the top

The differential harness started at the decision procedure and had to be pushed down twice,
each time finding a bug that the layer above could not see.

1. **The word layer.** `random_expressions_agree_with_enumeration` builds random expression
   trees over two 8-bit variables and compares `prove` against enumeration over all 65 536
   inputs. Mutation-validated: an Xor bug was caught (it claimed `(!b) == b` valid).

2. **The predicate layer.** `random_predicates_agree_with_enumeration` builds random
   comparisons over random word expressions combined with and/or/not/implies. This found
   DEFECT 15: a mixed-width operation silently truncated, so `trunc2(b) + (a + 115)` was
   computed in two bits and a refutable predicate read as `Valid`. Both `evaluate_pred` and
   the BDD agreed with each other because they share the constructor that was wrong; only
   enumeration disagreed.

3. **The weakest-precondition layer.** `wp_matches_concrete_execution` builds random
   straight-line and branching programs, evaluates the generated `wp` at all 256 inputs, and
   compares against a concrete interpreter. It is exhaustive and does not touch the BDD
   engine, so it tests the substitution machinery on its own. This found DEFECT 19: `subst`
   walked a shift amount as if it were a term id, which on a two-line program recursed
   forever and blew the stack.

Each layer needs its own oracle. When a bug is found, the oracle is usually the only thing
that disagrees -- which is the point.

## A field is not a term id just because its neighbours are

`Node.b` is a term id for most operations, but it is a *payload* for `Trunc` (source width)
and `Shl`/`LShr`/`Shr` (shift amount). Every traversal that reads `n.b` as a term has to
carve out those four ops. `blast` and `eval_term` do; `subst` did not, and that was DEFECT 19.
The symptom was not a wrong answer but unbounded recursion: term id 3 named a term that
contained the shift, so the walk never bottomed out.

When you add a traversal over `Node`, list the ops whose fields are payloads and handle them
explicitly. The compiler cannot help, because a shift amount and a term id have the same
type. Grep for `Term(n.b)` and check each site.

## A printer is part of the proof

`smtscript.rs` turns the engine's formula into SMT-LIB2 so an independent solver can
reproduce the proof. That makes the printer soundness-critical: if it prints a different
formula, the external evidence does not apply. Three bugs, all found by reading the output:

1. **Polarity.** A one-bit word used as a proposition printed as `(= w 0)` while the comment
   said `w != 0`. `truth(false)` came out as `(assert false)`, which every solver reports
   `unsat` -- so an external checker would call an impossible obligation proved. `distinct`
   is the spelling of `!=`.

2. **Sort.** `not`, `and`, `or`, `xor` exist in both readings, and the printer always used the
   bit-vector operator, so `not(x == y)` became `(bvnot (= x y))` -- ill-sorted, since `bvnot`
   wants a bit-vector and a comparison is a boolean. The width decides which spelling is valid.

3. **Direction.** `truncate` widens as well as narrows, and the printer used `extract` for both,
   so a widening `truncate` produced `((_ extract 15 0) x0_8)` -- extracting bit 15 from an
   8-bit vector. Widening is `zero_extend`.

The lesson is that a comment stating the intended semantics is not a check. Two of the three
bugs were under a comment that described the correct behaviour.

## A hazard you can detect beats a hazard you document

The twelfth hole stamped `Certificate` and `Implication` with an arena generation. The
thirteenth did the same for `Report`. The fourteenth asked the obvious follow-up -- what
*else* carries a term id? -- and found `Var`, `Pred`, `Mem`, `Query`, none of them stamped.
A stale `Var` through `prove` overflowed the stack, which is exactly what the `with_fresh`
comment had always said would happen:

  use-after-free in the term arena ... typically shows up as unbounded recursion rather
  than a clean panic

The comment was right. It had been right for many rounds while I read past it, and the
reason is worth writing down: it described the *symptom* rather than the *invariant*, so it
read like documentation of intended behaviour instead of a bug report about missing checks.

Two lessons.

1. Stamping types one at a time is whack-a-mole; the next type forgets. The fix is a check
   where the data lives -- term ids record their creating generation, and the arena's term
   accessors note a mismatch -- so every handle-carrying type is covered by construction.

2. The first version of the check still overflowed. It tested the current node, and a
   constructor can read a stale node then build a *current* node referring back to the stale
   id, giving a cycle whose every node is current. Guarding the root is not guarding the
   traversal: once anything stale is touched, the whole walk has to stop. I only found this
   because I ran the probe and watched the stack blow, after having convinced myself the fix
   was complete.

## A proof object has a lifetime the type does not encode

The twelfth hole, and the most serious one: `Certificate` stored a `Pred`, which is a term
*id*, and `with_fresh` resets the arena so ids restart at 0. A certificate from one scope named
a different formula in the next, and `weaken_to` returned a certificate for a statement the
engine itself refuted:

  scope A statement id : Pred(Term(2))
  scope B predicate id : Pred(Term(2))     <- id recycled
  same id?             : true
  prove(cert.statement()) in scope B : Counterexample
  cert.weaken_to(y < 200) -> true          <- a certificate for a falsehood

The engine knew the statement was false and the certificate claimed it proved. The comment on
`with_fresh` warned about this in so many words — "use-after-free in the term arena" — and the
warning did not help, because a warning is not a check and the failure is silent rather than a
panic. A proof object whose meaning changes underneath it is worse than one that panics.

Fixed with an arena `generation` bumped by every reset; `Certificate` and `Implication` record
it, and every rule re-checks it and returns `None` on a mismatch.

Two general lessons, both about handles.

1. An id into a reusable arena is a *pointer*, and a pointer with no generation is dangling
   after a reset. If a type is designed to outlive the scope that created it, it must carry
   whatever makes it valid, and the rules that use it must re-check. "One `with_fresh` per
   proof" is a convention; the generation is a check, and only the check survives a caller who
   did not read the comment.

2. A documented hazard is not a handled hazard. This project treats an unbacked claim as a
   defect; a comment warning that a thing will corrupt the arena is an unbacked claim about
   *safety* unless something enforces it. When a comment says "do not do X or Y happens", ask
   whether Y is caught or merely described.

## A stamp that the reset rewrites cannot detect a reset

The generation check above was itself defeated by the table it lived in. `term_gen[slot]`
recorded the generation that created the term in `slot`, and staleness was
`term_gen[slot] != generation`. But `reset()` is exactly the event that both recycles slot
numbering *and* leaves `term_gen` in place, so the next `mk_term` writes a *current* stamp
onto whatever term lands on a stale handle's slot. A `Pred` saved from one arena was then
discharged against a term it had never seen:

  `x == 1 && x == 2` (false for every `x`), saved in arena A
  arena B: build enough terms to reach A's slot
  `saved.prove()` in arena B : `Valid`          <- a proof of a false statement

The check compared the *slot's* stamp, which the recycling event rewrites; it had to compare
something the recycling event cannot touch. The generation is now packed into the id itself
(`Term::pack(slot, generation)`), so `is_stale` compares the handle's own bits. The lesson
generalises: an id that can be recycled needs its generation *inside the id*, because a side
table indexed by the recycled key is written by the same event that invalidates the handle.
`reset()` also keeps the generation non-zero and inside the bits a handle can hold, so the
sentinel's generation never matches a live arena.

The general auditing question, alongside "is the conclusion true" and "is the premise
reachable": **does the thing that invalidates the handle also rewrite the evidence used to
detect the invalidation?** If so, the check cannot fire.

## A refusal has to outrank the verdict it produced

Guarding a malformed term at the point of construction is not enough when a second entry
point can reach the same term. `word(1, 65)` built a term the bit-blaster's `[u32; 64]`
buffers could not hold; the blaster indexed `out[64]` and *panicked inside the solver*, so a
malformed specification became an unwind rather than an `Unknown`. Two fixes, both needed:
the width is refused where the term is built (`word`), and refused again at the blaster's
entry (`smt::Ctx::blast` and `bitblast::blast` mark the query ill-formed). The second matters
because a term can arrive by a path that skipped the first — a future constructor, or a
deserialised term — and the buffer bound is the invariant, not any single constructor.

The subtlety is that the SAT blaster marks the query and *returns*, and the caller had already
computed a verdict from the (now-meaningless) CNF. So the query layer had to check
`ill_formed` (and `stale`, and `var_overflow`) *before* reading the verdict: a refusal is only
a refusal if it wins. When adding a "mark and continue" path anywhere, check that every reader
of the result consults the mark.

## A report is valid only in the arena that produced it

`wp::Report` holds `Obligation`s, and an `Obligation` is a term id plus the generation that
created it. `Obligation::discharge` answers `Unknown` once the arena has moved on, so a report
that outlives its `with_fresh` scope *fails safe* — but it fails, and the example
`examples/pipeline.rs` was reading a report built in one scope after a second `with_fresh` had
already reset the arena. It happened to work only because no reset intervened before the read;
one more statement would have flipped every verdict to `Unknown`. The example now discharges
each report inside the scope that built it and lets only the self-contained SMT-LIB2 text
escape. The rule for callers: if a value holds a term id (`Report`, `Certificate`,
`Implication`, `Query`), consume it before the next `with_fresh`, or carry the generation and
re-check — never assume the arena is still the one you built in.

## The abstraction is where the claim lives

The eleventh hole was `Verified<T>`: it documented itself as "a machine-checked claim that the
associated contract was proved" while storing no contract and accepting any certificate. A
kernel test proved `x <= 255` and wrapped `42u32`, and it passed. The type name asserted a
connection that did not exist.

Two lessons, and the second is the sharp one.

First, an abstraction's doc comment is a claim like any other, and it can outrun the code the
same way a summary can. When the type is *named* for a guarantee, the name is the claim, and it
needs the same suspicion as a printed verdict.

Second: I tested the fix with `prove_equiv(v.statement(), x.le_val(255))` and it passed against
a deliberately broken wrapper. Of course it did — every certificate is a theorem, and every
theorem is equivalent to `true`. A semantic comparison cannot distinguish theorems, so it has
no teeth for checking *which* theorem was recorded. Structural equality does. The general
point: when testing that an object records the right thing, compare structure, not semantics;
if the object is constrained to be provable, semantics is constant and the test is vacuous.

## The exporter emitted formulas no solver would accept

The SMT-LIB2 exporter's doc said the boolean and one-bit-vector readings of `and`/`or`/
`xor`/`not` "coincide, so treating them as boolean is safe". They coincide *semantically*
and not *syntactically*: SMT-LIB is strongly sort-checked, and `Bool` is not `(_ BitVec 1)`.
Printing a one-bit connective in a bit-vector position produced

    (bvule (_ bv1 1) (or (distinct ...) (distinct ...)))

which every compliant solver rejects. The failure mode is the worst kind for this module:
the export exists so an *independent* solver can check the proof, and an ill-sorted file is
not a failed check but no check at all -- the independence claim is quietly void.

It was found only by handing the text to a real solver. Unit tests asserted the *shape* of
the output and passed; a z3 differential over random predicates failed on 77 of 800 cases,
all of them width 1 or a comparison in a word position. Hand-wavy "the truth tables agree"
reasoning is not a substitute for running the artifact through the consumer.

The fix renders from the expected *sort*, not the node's own width: `Bool` prints
comparisons natively and one-bit connectives as `and`/`or`/`xor`/`not`; `Bits` prints
comparisons as `(ite <cmp> (_ bv1 1) (_ bv0 1))` and one-bit connectives as
`bvand`/`bvor`/`bvxor`/`bvnot`. A comparison's spelling lives in its own `Cmp` printer
because both contexts need it -- and because `Bool` delegating to `Bits` which delegates
back to `Bool` for the same node recursed until the stack overflowed, which the first
attempt at the fix did.

## Third time: the call arm

After `if` and `while` came the call, the third construct whose right-hand claims were
checked in the wrong state. `a := 5; c := double(a); assert c == 10` was refuted with `c`
free, even though the callee's contract says `c == a + a == 10` and the `CallRequires`
obligation was discharged.

The fix differs from the other two in a way that matters, and getting it wrong would have
looked like success. `if` and `while` describe their entry state in the *same* variables,
so wrapping the claim with `guard_range` suffices. A call *renames* every written target
(that is the havoc that keeps pre- and post-call values apart), so the goal must be
substituted too. Wrapping alone would leave `implies(v == a + a, c == 10)` with the old `c`
still free -- still refuted, the change inert. The arm therefore substitutes the goal by the
havoc list *and* wraps it, which `guard_range` cannot express.

The pattern to carry forward: after a `while` or a call, a claim to the right is checked
under that construct's exit assumption, and the transformation must touch both the
assumption and the goal. `Assume` is the fourth instance of the same family and already does
this via `guard_range` plus `*cursor = implies(*c, *cursor)`.

## The same defect, one construct over

An assertion after an `if` was checked as if the `if` were absent (a false refusal, fixed
by rewriting the claim to `wp(if, g)`). The loop arm had exactly the same hole and was not
touched by that fix: an assertion after a `while` was checked in the *pre-loop* state.
`while x < 3 inv x <= 3 { x := x + 1 }; assert x >= 3` came back refuted with counterexample
`x = 0` -- the entry state, which the loop body never leaves untouched -- while the loop's
own `LoopExit` obligation, `inv && !guard => q`, proved the very same claim.

The tell is that the loop *already computes* the context the claim needs. `LoopExit` is
`inv && !guard => q` for the continuation `q`; a claim to the right of the loop is the same
`q`, so it wants the same context, `inv && !guard`. Fixing one construct does not fix its
sibling, and the sibling is found by asking where else the same expression is built: search
for the *shape*, not for the bug.

`LoopExit` itself must not be wrapped again -- it already carries its context, and
`guard_range`-ing it would only weaken a correct obligation. The rewrite is applied to
slots strictly to the right of the loop (`start..entry_n`), which is why `entry_n` is
captured before the loop's own obligations are pushed.

## A kernel rule with no bounds proves anything

The `Theorem` impl for `Imp` was

```rust
impl<P, Q> Theorem for Imp<P, Q> {
    type Proof = ImpProof<P, Q>;   // the *propositions*, not their proofs
}
```

There is no bound on `P` or `Q`, and the associated type names `P` and `Q` rather than
`P::Proof` and `Q::Proof`. So `assert_proof!(Imp<Truth, Falsity>)` compiled: the kernel
accepted `Truth => Falsity`, a falsehood, while correctly rejecting `And<Truth, Falsity>` and
`Equals<u8, u16>`. The module's doc says "if the reasoning is wrong, the program does not
compile", and it was false for the one connective that carries reasoning. The fix is both
bounds and the proof types:

```rust
impl<P: Theorem, Q: Theorem> Theorem for Imp<P, Q> {
    type Proof = ImpProof<P::Proof, Q::Proof>;
}
```

Two things had to be true for this to survive, and both are worth checking for elsewhere.

1. **A missing bound is invisible until something requires it.** `And` and `Equals` carry
   bounds (`P: Theorem, Q: Theorem`; `impl<A> Theorem for Equals<A, A>`), so a false `And` or a
   false `Equals` fails to compile. `Imp` did not, and nothing noticed, because the only way to
   notice is to ask for the proof of a false implication -- which no test did.

2. **A constructor that does not type-check against the associated type is a warning nobody
   reads.** `imp_intro` and `modus_ponens` already used `P::Proof`/`Q::Proof`, so they returned
   `ImpProof<TruthProof, TruthProof>` while the associated type was `ImpProof<Truth, Truth>`.
   That mismatch is a compile error the moment a test *names* the associated type, and no test
   did. The regression test now names it, and the `compile_fail` doctest
   `assert_proof!(Imp<Truth, Falsity>)` is the teeth: reverting the impl turns it red.

The general rule for a proof kernel: every connective needs a `compile_fail` example for a
*false* instance of it. A kernel is only as strong as its weakest rule, and the untested rule
is the one that is wrong.

## A guard can be correct and still be untested

While sweeping for the ninth hole I checked `MAX_VARS`. `var_term` refuses an index past the
cap by setting `overflow` and returning `Term(0)` — and `Term(0)` is a *valid* node, so the
guard is what keeps a query from answering about the wrong term. `query_valid` and `query_model`
both check it and return `Unknown`. No test touched it.

I predicted the unguarded failure would be a false `Valid` (a proof of a false statement).
Measured, it is a bogus **witness**: `prove(v300 == 0)` comes back `Counterexample(v0 = 1)`,
because the fallback made v300 alias v0, so the engine names a variable the query never
mentioned. Wrong prediction, and the measured version is the more useful fact.

Two lessons. First, a guard that is correct is not the same as a guard that is tested — the
whole overflow path was dead to the suite. Second, and this is the recurring one: I predicted a
failure mode and it was wrong, which is why the test comment now records what was measured
rather than what was expected. Prediction is cheap; the probe is what counts.

Both directions are pinned: `exceeding_max_vars_reports_unknown_not_a_proof` and
`a_query_within_max_vars_is_decided_normally`, so the guard cannot pass by answering `Unknown`
to everything.

## The evidence for a refutation is also a claim

The ninth hole was in `Cex`: the model returned with a `Counterexample` verdict. It inlines 16
assignments, `model` stopped at the cap silently, and `value_of` returned `None` for a dropped
variable exactly as for an untouched one. So a caller could not tell an incomplete witness from
a complete one, and a witness is the *evidence* for a refutation.

That is the same class from a third angle. The first five holes let a **summary** outrun its
evidence; the sixth and seventh gave a **proof** with no evidence; the eighth gave an ambiguous
**negative**; this one gives a **witness** with a hole. In every case the object claims more
coverage than it has. So the sweep question generalises:

6. When something is reported as a *result* — a verdict, a summary, a witness, a count — does
   the type say what it covers? The negative and the positive both need the answer, and the
   fixed-size buffer is where the coverage quietly shrinks.

`Cex` now carries `total` alongside `n`, `is_complete()` compares them, and `Display` prints
`TRUNCATED`. Nothing else in the crate consumed `Cex` fields, so the fix is contained.

## An ambiguous negative is the same bug as a silent truncation

The eighth hole lived in `find_counterexample_by_enumeration`, the function the tests use to
check the engine. It took a `limit` and returned `Option<u64>`, so `None` meant either "swept
the whole domain, nothing violated" or "stopped early, nothing violated". Searching a prefix of
the domain reported no counterexample for a property that is false.

That is the recurring class one level up: not a limit that truncates a *result*, but a limit
that truncates the *search* and then reports the same value as a complete sweep. The tell is a
negative answer whose type does not say what was covered. So:

6. When a function returns "nothing found", `false`, or `None`, does the type say whether the
   whole space was covered? If a caller can pass a smaller space and get the same answer, the
   negative is ambiguous, and it will eventually be read as a proof.

The fix removes the choice rather than documenting it: the parameter is now the domain size,
derived by `domain_of_bits(bits)` from the input width, and the return is `Search::Witness` or
`Search::NoWitness`. Checked while sweeping: `exhaustive.rs` is safe because its domain is the
type itself and its loop uses `checked_add`.

## Quote the count, do not remember it

Three commits in a row said "161 tests pass", "163 tests pass", "165 tests pass" while the
real numbers were 149, 151, 153. Every other figure in those messages was measured -- the
differential case counts, the mutation counts, the coverage counters. The test total was the
one number I recalled, and it drifted by a constant twelve, which is the signature of counting
something else once (test functions plus doc examples, probably) and then incrementing from
memory.

The failure is the same class as the seven holes, in the reporting rather than the code: a
number stated with more confidence than the evidence behind it. The fix is the same shape too
-- do not argue it, measure it. `scripts/test-count.sh` runs the suite and prints the exact
count, so the figure is a command rather than a memory. Run it before writing the number.

If a claim is worth putting in a commit message, it is worth the command that produces it.

## A literal is a claim about a width

`word(v, w)` truncated `v` to `w` bits. `word(300, 8)` was the same term as `word(44, 8)`, so
the DSL expression `x + 300u32` on a `u8` silently meant `x + 44`, and the engine would
happily return a counterexample or a proof about a constant nobody wrote. `eq_const` already
refused an out-of-range constant, so the two spellings of the same intent disagreed -- a
sure sign that one of them was wrong.

`word` now marks the term, and the query answers `Unknown`. The one legitimate use of the
truncation was the "all ones" idiom, `word(u64::MAX, w)`, used for a mask or a maximum; that
is now `all_ones(w)`, which says what it means and does not read as a 64-bit constant.

Two lessons.

1. A helper that takes a value and a width has a contract, and "it fits" is part of it. When
   the type system cannot express the constraint (a runtime `u64` and a runtime width), the
   check has to be explicit and the failure has to be *visible* -- here, a refusal rather
   than a wrapped value.

2. When two entry points express the same idea (`eq_val` and `x + k`), test that they agree.
   The disagreement was the bug, and it would have been caught by a one-line differential
   test between the honest spelling and the convenient one.

## Vacuity is not only about widths

The sixth hole was vacuity caused by a width: a bound too narrow to name `len`. The seventh is
the same failure with no width involved at all -- `verify(s, pre, post)` with an unsatisfiable
`pre`. The condition `pre => wp(body, post)` is a theorem for *any* body and postcondition
when `pre` is unsatisfiable, so the report said `Total` about `x := 0` proving `x == 99`.

The lesson is that vacuity is a property of the *premise*, not of any particular construct.
Every entry point that takes a predicate and proves something under it has to ask whether the
predicate can hold:

* a top-level precondition (`verify`, `verify_proc`);
* a guard or a range that could be empty (`forall_guarded(lo, hi, ..)` with `hi <= lo`);
* a width, mask, or cap that makes a named value unreachable (the sixth hole).

Swept so far: `mem` (width), `verify` (unsatisfiable precondition). `quant::forall_guarded`
and `exists_guarded` are *not* affected: an empty range yields `true`/`false` respectively,
which is correct for an empty range, and `inside` already treats an unrepresentable index as
outside the bound rather than truncating it.

## A differential test that fails on a correct program is a bug in the test

The soundness families in `tests/modular_differential.rs` check one direction: if the engine
reports verified, no concrete execution violates the postcondition. That direction cannot see
over-refusal, and over-refusal is exactly what the two defects above were -- so the new
assertion family checks both directions:

> verified if and only if no concrete execution reaches a failed assertion.

Both defects 36 and 37 are caught by it. The teeth were confirmed by reverting each fix in
turn: without the branch guard the family reports "every concrete run is fine but the engine
refused the program", and dropping the assertion obligation outright makes it report "the
engine verified a program whose assertion fails on a real input".

The family also cost an afternoon to a phantom soundness hole, and that is worth recording.
The concrete interpreter threaded the state *by value* into the recursive branch call, so every
assignment made inside an `if` was lost. The engine was right and the interpreter was wrong, but
the failure message said the engine had verified a program with a real violation -- the most
alarming message a verifier's test suite can produce. The lesson is the ordering of suspicion: a
differential test that disagrees with the engine on a *correct* program is almost always the
test's bug, and the interpreter is the less-trusted component, because it is the newer and less
carefully reviewed one. Thread the state by `&mut` through branches.

## A claim after a statement is made in a state that statement can produce

An assertion recorded to the *right* of an `if` is dominated by it, so its claim is
`wp(if, g)`, not `g`. The walk already rewrote dominated claims through `Assign` and
`AssignMany`, but not through `If`, so `if x == 1 { x := 1 } else { x := 2 }; assert x == 1 ||
x == 2` was reported as a failure while the contract obligation proved it -- the assertion was
checked as if the `if` were not there. The `If` arm now rewrites the slots recorded before it
with `ite(cond, wp(then, g), wp(else, g))`.

This is the mirror image of the previous defect and it is worth seeing the pair together:

* a claim *inside* a branch is checked under the branch's guard (`guard_range`), because the
  branch is what reaches it;
* a claim *after* the branch is checked through the branch's effect (`wp_of`), because the
  branch is what the state came from.

Both are "the claim is about the states that can reach it", read in the two directions. A
statement that changes the state has to reach every claim it dominates, and an `If` was the
one statement that did not. Loops are deliberately excluded: a loop's effect on a claim after
it is only the invariant, and the cursor already carries that, but a dominated assertion is
not re-derived through a loop for the same reason loop obligations are not rewritten with a
dominating guard -- the invariant is universally quantified and rewriting through it would
hide a real failure behind a vacuous one.

## A claim is made in the state that reaches it, not in the state after it

An assertion recorded as `implies(cursor, c)` is the wrong claim. The cursor is what the
*continuation* needs, so `implies(cursor, c)` says "if whatever comes after this assertion is
satisfiable, then `c`". That is not what `assert c` means, and it has two consequences.

The visible one is that correct programs were refused. `if x == 1 { assert x == 1 }` was
reported as a failure, because the assertion was checked against every `x` rather than the `x`
the guard admits -- so an assertion inside a branch could never be used. `wp.rs` documented the
opposite ("checked in the context of the state that reaches it"), and no test exercised an
assertion inside a branch, so the documentation and the code disagreed and nothing noticed.

The assertion's goal is now just `c`. The state that reaches it is fixed by two mechanisms,
and keeping them separate is what makes the guard correct:

* assignments that dominate the assertion are applied as *substitutions*, in the backward
  walk, so `x := 5; assert x == 1` becomes `assert 5 == 1`;
* guards, loop invariants and dominating `assume`s are attached as *context*, by
  `guard_range`, after the branch or body has been walked. Wrapping `c` in `g => c` at the
  enclosing construct keeps `g` about the entry state. Substituting `g` in instead would let a
  write inside the branch rewrite the guard, which turns `if x == 1 { x := 5; assert x == 1 }`
  into a green check.

`guard_range` applies to `Assertion` and `CallRequires` obligations only. Loop obligations are
universally quantified over the loop-head state and already carry their own context; rewriting
them with a dominating guard is the vacuity bug they exist to avoid.

## One variable index is one variable, at one width

The blaster keys its BDD variables by `(index, bit)`, and a variable's index is what
`var_named` sets. Declaring the same index at two widths therefore aliases the low bits:
`var_named(0, 8)` and `var_named(0, 16)` share bits 0..7, so `a == 3 => truncate(b, 8) == 3`
came back `Valid` -- a theorem about one variable silently constraining another. The engine
even handed back a counterexample naming one `(0, 16)` assignment while the model also touched
`(0, 8)`, because the model builder reports one entry per index.

`var_named(idx, w)` called twice at the same `w` is the intended "name a variable for a
readable model" case and stays allowed; calling it at a *different* width is a modelling
mistake, and the query is now refused. The general rule: if a name carries an index, the
index has to determine the variable completely, or the name is not a name.

## A missing conjunct hides in the ranges the tests do not use

`verify_bounded_sub_is_total` states the refinement of `Bounded::sub`. Its doc named three
conjuncts -- no underflow, result at or above `min`, and (free) at or below `max` -- and the
goal carried only two, as `iff(in_range(diff), want)`. The underflow gate `b <= a` was on the
right side but not on the left, so the left side asked whether the *wrapping* difference is in
range.

For the ranges the tests used that is the same question. A narrow range makes an underflow wrap
to a value above `max`, so `in_range(diff)` is false and the two sides agree. Every test used
`min`/`max` inside `[0, 1000]`, and all of them passed. At `min == 0`, `max == u32::MAX`, an
underflow wraps to a value that is still `<= max`, so the left side is true while `checked_sub`
returned `None`: the goal became `true <=> false` and the obligation was refuted. It was never
proved for a wide range at all.

The fix is to gate the left side exactly as `checked_sub` does -- `result_ok = no_underflow &&
in_range(diff)` -- and the new tests pin both the full range (it must now be proved) and the
ungated statement (it must still be refuted there, so the gate cannot be dropped again).

The general lesson is about the *test inputs*, not the formula: a proof obligation parameterised
by `min`/`max` is only as strong as the ranges the tests exercise. A boundary that the tests
never approach is a boundary the formula is free to get wrong, and a parameter that is always
zero or small in the tests is nearly a parameter the proof does not use.

## A proof that never mentions the thing it is named after

`verify_scale_identity` was documented as proving `k * SCALE / SCALE == k`, but its formula
was the `verify_fixed_roundtrip` proof with the local variable names changed: `shl(k, 4)` then
`lshr(..., 4)`. No scale factor appeared anywhere. The identity therefore held for *any* scale
value, because the scale was never an input -- a multiplication by 10 instead of 16 would have
"satisfied" it just the same. The function had a name, a doc comment and a passing test, and it
proved the roundtrip lemma a second time.

The fix is to actually multiply by the scale before dividing. The tell is general and cheap to
apply: read the formula and check that every noun in the doc comment appears in it. A verifier
whose name mentions a constant, a mode, a bound or a factor must have that thing as a term in
its goal, or the parameter is decorative.

## A proof about the wrong quantity

`verify_saturating_add_bounds` was documented as "the saturating result is always `>= a` and
`>= b`", but the formula never built the saturating result. It proved a *conditional* statement
about the *wrapping* sum, `a <= sum => (a <= sum && b <= sum)`. The hypothesis it carried is the
complement of the case that matters: saturation is interesting exactly when the sum overflows,
which is when `a <= sum` is false. So the one scenario the function is named for was excluded by
its own precondition.

The goal is now unconditional and about the saturating value. The test also asserts that the
wrapping sum violates the bound for some input, so the `ite` cannot be dropped.

The tell, shared with the earlier vacuity defects: the comment and the formula are about
different objects. Read the formula and ask which term in it is the one the comment names.

## Prove the property the comment claims, at the boundary

Two verifier functions in `logic.rs` proved a true statement that was one step weaker than the
claim their comments made, and the gap was exactly at the boundary:

* `verify_fixed_add_no_overflow` concluded `sum <= 2^15` while the comment said the sign bit
  stays clear. `2^15` *is* the sign bit. At the stated inclusive bound `2^14` the sum
  `2^14 + 2^14 = 2^15` reads as `-32768` in a signed 16-bit add. The bound is now `2^14 - 1`
  and the goal is `sum <= 2^15 - 1`.
* The tenth "algebraic identity" was `ult(x, 0) <=> false` with the comment "x < 2^w". That is
  a tautology of the encoding -- an unsigned value is never below zero -- and it is unchanged
  by substituting *any* term for `x`, including a constant, so it proved nothing about `x`.
  It is now `x <= all_ones(w)`, the range law the comment described.

Both are the same mistake: the comment and the formula describe different propositions, and
the formula is the weaker one. A verifier function is read by its comment; if the comment names
a bound, the formula has to prove *that* bound, at *that* boundary, including the endpoints.

## A parameter the proof never mentions is a parameter the proof cannot use

`verify_bounded_sub_is_total(min, max)` proved the refinement invariant of `Bounded::sub`, but
the formula dropped `min` outright (`let _ = min;`) and the doc claimed "in range exactly when
`a >= b`". That claim is false for any non-zero `min`: at `min == 10`, `a == 11` and `b == 10`
are in range and `a >= b`, but `a - b == 1` is below `min`, so `sub` rejects it. The proof
succeeded because it no longer mentioned the parameter it had been given.

The corrected obligation is `in_range(diff) <=> (b <= a && diff >= min)`, with the `min`
conjunct doing real work, and the test now states the claim *without* that conjunct and shows
it is refuted. The pattern to watch for: a verifier function that takes a parameter and
discards it. `let _ = min;` is a confession that the formula and the signature have drifted
apart, and the honest response is to either use the parameter or remove it.

## A sufficient condition that goes vacuous is not a proof

`verify_accumulator_no_overflow` proved "the sum cannot wrap" as `sum <= 2 * max`. That is a
sufficient condition only while `2 * max` fits the width. When it does not, `ule_const` reads
the bound as "every value is below it" and answers `true`, so the obligation was *vacuously*
proved for exactly the `max` values whose sums overflow. `verify_accumulator_no_overflow(8, 200)`
returned `Valid`, though 200 + 200 = 400 wraps to 144 in 8 bits. This is the whole safety
argument for an accumulator, so the vacuity sat on the most load-bearing proof in the module.

The fix is to test the property itself rather than a bound on it: a sum wraps exactly when
`sum < a`, which is width-independent and needs no side condition. The lesson is that any
"check `x <= bound`" goal has a `bound` large enough to make the check vacuous, and a proof
obligation must be phrased so that no value of its parameters can make it trivial. When the
goal mentions a constant, ask what happens when that constant is at the edge of its range.

The test now asserts the positive case *and* the four refutations, checking they come back as
counterexamples rather than merely "not proved", so a future fix that returns `Unknown` for
everything cannot pass it.

## Refuse an ambiguous assignment, do not pick one

`substitute` applied its bindings in order and kept the last for a repeated target, so a
simultaneous assignment written `x := 1, x := 2` proved `x == 2` -- a claim about a value that
appeared once in the list and lost. Reordering the same bindings proved `x == 1`. Both are
silent choices of one meaning among several, which is the failure this crate exists to prevent;
the honest answer is `Unknown`.

The refusal reuses the query-level ill-formed flag, which already covered a width clash and an
out-of-range constant, and is now named `ill_formed` rather than `width_clash` because it no
longer means only widths. Two different targets still substitute normally, which the test
asserts so the check cannot pass by refusing everything.

The general rule: when a list admits two readings, refuse. "Last one wins" is a convention, not
a specification, and it is invisible at the call site.

## A binding target must be a variable

`substitute` read a binding's left-hand side as `node_of(from).a`, with no check that `from`
was a variable. But `a` means different things per operation: for a `Var` it is the index, for
a `Const` it is the *value*, and for `Trunc`/`Ite` it is a *term id*. So binding the constant
`word(7, 8)` -- whose `a` is 7 -- silently substituted variable index 7, and a program that
"assigns" to a constant proved `v7 == 0`. A binding to a `Trunc` read a term id as an index,
which either fell outside `MAX_VARS` and was dropped, or named an unrelated variable.

None of these are refusals; they are silent rewrites of the wrong variable. The fix is that
the target must be `Op::Var`, asserted. The general pattern: `a` is an overloaded field, so
every consumer has to know which operation it is reading before it can interpret `a`, and the
only safe default is to check the operation first.

## The shift amount is a literal too

The out-of-range constant bug (`word`) had a twin in the exporter. A shift amount is printed
as a literal of the shift's width: `(bvshl x (_ bv300 8))`. `300` does not fit 8 bits, so that
is not a legal 8-bit literal -- a solver rejects the file or reads 44. And for `k >= 2^width`
the *wrap* changes the meaning: `shl(x, 256)` printed `(_ bv0 8)`, the identity, while the
engine's rule is that a shift of at least the width yields 0. So the exported file disagreed
with the engine on a legal program.

The engine's rule makes every amount `>= width` equivalent, so the exporter clamps the printed
amount to `width`: a legal literal with the same meaning. It is the same "a literal is a claim
about a width" mistake as `word`, in a different place, which is why it is worth stating as a
pattern rather than as a one-off.

The first export fuzzer could not have found it: its shift amounts were always `<= 8`, and the
bug lives at `>= 2^width`. A generator that only emits well-behaved inputs checks only the
well-behaved paths. The amounts now span `0..=11` (including `k == width` and just past it),
and a dedicated test drives `k` in `{8, 9, 255, 256, 300, u32::MAX}` and compares the parsed
meaning against the engine's rule for every input.

## Two rules, one program: `verify` and `wp` must agree

`verify` runs `collect`, which checks `Stmt::frame` at every call and reports a bad frame as
an obligation. `wp::wp` is *also* public -- it is the rule a caller uses to build a weakest
precondition by hand -- and it applied the same call rule *without* the frame check. So the
two entry points disagreed about the same program.

The consequence was a false proof, not a missing one. A callee whose body zeroes `g`, called
with an empty declared frame, havocs nothing under the old `wp`, so `wp(call, g == 7)` was
just `g == 7`, and `g == 7 => wp` came back `Valid`: a proof that the callee's write did not
happen. `verify` rejected the same call.

The fix is that `wp_of` checks the frame too, and returns `false` when it fails -- there is no
report to carry the failure, and the honest weakest precondition of an unmodelled call is
`false`. The general lesson: a second entry point into one rule is a second chance to forget
a precondition, and the tests have to drive *both*. `tests/call.rs` now has
`wp_refuses_to_reason_about_a_call_with_a_bad_frame` (the bad frame) and
`wp_still_reasons_about_a_call_with_a_good_frame` (a framed call still works), because a fix
that returned `false` for every call would pass the first test alone.

## A test that passes by failing to parse

The first version of the independent SMT-LIB reader could not parse `((_ extract 7 0) x)` --
a standard *indexed application*, whose head is itself a parenthesised `(_ ...)`. It handled
only the self-contained literal `(_ bvN w)`, which has one `(`.

That bug made a "teeth" test lie. `the_export_checker_rejects_what_the_old_exporter_printed`
asserted that `extract` past the end of a vector is rejected, and it was -- but by a *parser
error* at byte 10, not by the sort check the test is named for. Worse, every well-formed
export containing an `extract` or a `zero_extend` was rejected too, so the new
mixed-operator fuzzer failed on correct output.

Two things follow. First, a rejection test needs a positive control: the same test now asserts
that a well-formed `extract` and `zero_extend` *parse*, so it cannot pass by refusing
everything. Second, "the checker rejects X" is only evidence of a sort check if the checker can
parse X's valid neighbours. When the checker is the oracle, its own parser is part of the
thing under test.

## Read the printer with a parser, not with your eyes

Three defects in the SMT-LIB2 exporter were found by *reading* the output: an inverted
polarity, `bvnot` applied to a boolean, and `extract` for a widening truncate. Each was
invisible in the source -- `write!(f, "(bvnot {})", ...)` looks fine -- and each made the
external evidence not apply, because an ill-sorted file is rejected or misread.

The fix for "reading is not a check" is a second implementation. `tests/differential.rs` now
carries an independent SMT-LIB reader: it parses the export, rejects any ill-sorted operator
application (the three shapes above are its regression cases), and *evaluates* the parsed
term over all 65 536 inputs to compare against the predicate it came from. The exporter and
the engine are no longer the only two things that agree with each other.

The general lesson, and the reason it took three rounds: a printer's contract is
well-sortedness *and* meaning, and the two fail differently. Meaning you can only check by
evaluating; sort you can only check by knowing the operand types, which means the checker has
to be a type checker, not a text diff.

## Vacuity is a property of the *path*, not just the premise

The seventh hole was an unsatisfiable precondition. The next one is the same failure one
level down: an unsatisfiable `Assume` *inside* the body. `Assume(false); y := 0` with
postcondition `y == 99` came back `verified` / `Total`, because `false => wp(y := 0, y == 99)`
is a theorem. The contract was about code no run can reach.

The precondition check could not see it: the precondition was `true`, perfectly reachable.
Vacuity is not about the *entry* predicate, it is about whether any execution reaches the
code the proof is supposed to cover. Every construct that can cut a path has to ask whether
it did:

* a precondition (`verify`, `verify_proc`);
* an `Assume` inside the body -- this hole;
* a guard that is unsatisfiable, which the loop rules inherit from `Assume`-like reasoning;
* a branch condition that is a contradiction, which makes the branch vacuous.

`Assume` cannot simply be refused: a reachable `Assume` is how a callee guard or a
case-analysis split is written, and it must still verify. The check is "this `Assume` cannot
hold", not "there is an `Assume`", and the reachable case is pinned by a test so the fix
cannot degrade into refusing all of them.

## The dual class: vacuity, a proof with no evidence

Six holes now, and the sixth is the mirror of the first five. Those were *unsound*: a
summary (`verified`, `Total`, `Valid`, `unchanged`) stronger than the evidence behind it. The
sixth is *vacuous*: a proof whose evidence is empty.

`Mem::check_addr_width` accepted a bound exactly as wide as the address. A 2-bit bound on a
4-cell memory cannot hold `len`, so the standard postcondition `bound == len` was
unsatisfiable, and `bound == len => P` and `bound == len => !P` both proved. The tell is
unmistakable once seen: **an impossible precondition reported as valid.** Ask of any proof
not only "is the conclusion true" but "is the premise reachable". A verifier that cannot
distinguish `Valid` from `vacuously Valid` will certify a specification that constrains
nothing.

The fix is one bit: the bound must be strictly wider than the address. Every intended use
already passed a wider bound, so the check costs nothing and closes the trap.

Two auditing questions to add to the three above:

4. Can a precondition or guard be unsatisfiable, making the obligation vacuous? In
   particular, can a width, mask, or cap make a value that the specification names
   unreachable?
5. Is a proved obligation *sensitive* to the thing it claims to constrain? A mutation test —
   change the postcondition to something false and demand the proof fails — is the cheapest
   way to tell a real proof from a vacuous one.

That is what the memory positive family does: templates correct by construction, each with a
mutated twin that must be refuted. 140 proved, 134 mutations refuted, and the six survivors
are the `n: 0` boundary, asserted to be vacuous on purpose.

The trap also hides in the *width a claim is stated at*, not just in a bound. The
`flight_control` example proved `clamped <= 4095 => clamped * 1000 <= 4 095 000` at 16 bits,
where the product wraps to 16 bits: `scaled <= 4 095 000` is then true for every value (the
maximum is 65 535), so the implication holds for *any* antecedent and constrains nothing. The
example now models it at 22 bits — the first width that holds 4 095 000 — and asserts the
bound is refutable there before proving the implication, so a future narrowing of the model
fails loudly instead of passing vacuously. When a proof states a claim about an operation that
can overflow, check the modelled width can represent the result the claim names.

The *guard* that establishes this is itself a place to be vacuous, and was. It first read
`!prove(scaled.gt_val(4_095_000)).is_proved()`, but `scaled` is the **clamped** product, which
is at most 4 095 000 at every width: the predicate is `Unsat` at 22 bits *and* at 16, so the
negated `is_proved()` was true in both cases and the guard could not detect the narrowing it
existed to detect. The guard has to be stated over the **unclamped** product —
`find_model((raw * 1000u32).gt_val(4_095_000))`, requiring a `Counterexample` — which is
satisfiable at 22 bits (`raw = 4096`) and unsatisfiable at 16. Two lessons: a guard's predicate
must be over the quantity whose range the guard is about, not over a value already constrained
to be in that range; and `!is_proved()` is the wrong way to say "refutable", because it also
accepts `Unsat` and `Unknown`. The tests `the_vacuity_guard_{accepts,rejects}_...` pin both
widths, and `a_clamped_product_is_never_above_the_bound_at_any_width` records the fact that
made the old form vacuous.

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

The same "cover every module" rule caught `sym`, which had *no* test file at all. A DSL with
no test is a module whose surface is only ever exercised by the doc example, and the doc
example used one operator. Walking it turned up the missing literal `-` and `^` (see the
README). A module that only wraps other modules still needs its own tests, because the
*wrapping* is the code under test — an operator mapped to the wrong primitive is invisible to
every test of the primitive.

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

Fifth instance, found in the same session as the surface pass: the *public* `wp::obligations`
also returned a saturating count, so a caller inspecting obligations directly could not tell
a complete set of `MAX_OBLIGATIONS` from a truncated prefix. `verify` was never fooled — it
reads the internal flag and raises `Rule::ObligationOverflow` — but the public accessor was,
which is the point: **fixing a defect in one path does not fix the same defect in a sibling
path that re-exposes the same data.** When a fix adds a completeness flag to an internal
helper, walk every public function that wraps that helper and check it does not re-hide the
partiality behind the old return shape.

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

## Two paths for one obligation mean neither path's teeth are real

`wp` carries an `assert` two ways: as its own recorded obligation *and* in the backward
cursor that the enclosing rule consumes. Three defects lived in this area, and each was
found by a hand-built example rather than by a test, for a reason worth internalising:
breaking *either* path alone changes nothing observable, because the other still discharges
the claim. Only a mutation that breaks both at once — or that breaks the composition rule
they share — shows the harness is load-bearing.

The consequence for testing: when a mutation does not make a test fail, do not conclude the
test is weak. First ask whether the property is enforced twice. If it is, either break both
paths in one mutation, or aim the mutation at the shared rule. `LoopExit` dropped alone is
caught by `tests/loopdiff.rs`; the cursor's claim propagation dropped alone is not, and that
is a property of the design rather than a gap in the test.

## Teeth have to isolate the guard they claim to test

The mirror of the lesson above, and the opposite failure: a test whose teeth are never
pulled, because a *different* check refuses the input first. The test
`a_declared_frame_longer_than_the_cap_is_refused` was written to pin that `Stmt::frame`
refuses a declared frame with more than `MAX_CALL_ARGS` writes — the guard that keeps
`havoc_writes` from truncating. Its first version built a body writing `MAX_CALL_ARGS + 1`
variables, which the *derived-frame* check (check 0, `!derived.complete()`) refuses long
before the declared-frame cap is reached. So the test passed, and kept passing when the cap
check was deleted: it was asserting the wrong guard, and the mutation could not tell.

The fix is to make every earlier check pass, so only the guard under test can be what
refuses: a body writing a *single* variable (derived frame small and complete), distinct
globals, distinct images. Then removing the cap makes the test fail, which is the only
proof that the teeth are real. The rule: before trusting a rejection test, run the mutation
that removes the guard it names, and confirm it fails. If a nearer check could also reject
the input, the test is ambiguous and you cannot tell which check fired.

## A SAFETY comment is a claim, and it needs the same treatment as any other

The `no_std` `with_ctx` takes `&mut` to a `static mut`, and justified it with "the arena is
not `Send`/`Sync`". It was: every field of `Ctx` is a plain array or integer, so `Ctx` was
auto-`Send` and auto-`Sync`, and a `Sync` type can be shared across threads. The comment was
false, which is worse than absent — a reviewer checks the unsafe block against it.

The fix was not to reword it but to make it true: `Ctx` now carries
`PhantomData<*mut ()>`, the one pointer type with no `Send`/`Sync` impl. Verify this kind of
claim by asserting the trait bound in a scratch test and watching it fail. A comment that
names a mechanism the type system enforces will survive refactoring; one that names an
intention will not.

**Follow-up: the scratch test was not enough, so it is now a gate.** A scratch test that
was run once and deleted leaves the marker exactly as unprotected as the comment was — the
next refactor that drops `_not_shared` builds clean and the safety argument is false again,
with nothing to notice. `smt.rs` now carries a permanent `const _: fn() = || { ... }` that
fails the *build* if `Ctx` ever becomes `Send` or `Sync`. The mechanism is inference
ambiguity: `AmbiguousIfImpl<()>` is implemented for every type, and
`AmbiguousIfImpl<InvalidSend>` again for every `Send` type, so a `let _ = <Ctx as
AmbiguousIfImpl<_>>::some_item;` compiles only while `Ctx` is `!Send` (one applicable impl)
and is an `E0283` inference error the moment it is `Send` (two). `Sync` is checked the same
way. Teeth confirmed the only way that counts: removing `_not_shared` fails the build with
`multiple impls satisfying Ctx: AmbiguousIfImpl<_>`, and restoring it builds. The general
rule this is an instance of: a one-off verification of an invariant is not the same as a
gate, and only the gate survives the next change.

## The front end is total, and "it has never panicked" is not the same as "it cannot"

The MIR reader parses text the crate did not write — rustc's `-Zunpretty=mir` output, or
anything a caller hands `parse_program` directly. A panic on a shape it did not expect is a
crash in the caller's process, not a refusal, and the crate's whole posture is that an
unmodelled input is a refusal. So "the reader is total" is a property the safety story leans
on, and it was, until now, only an observation: nobody had seen it panic.

It is now a test, `mir::parse::tests::no_input_panics_the_reader`. The interesting choice is
the *input distribution*. A random token soup is cheap and reaches almost no parser state —
it fails at the first unexpected token, which is the easy path. What reaches the boundary
between states is a **valid dump with a few characters mutated**, so the corpus is two real
dumps with 1-12 single-character insertions, deletions and substitutions from a pool of
characters the reader actually reacts to. 20,000 such inputs, deterministic and seeded.

The test asserts three things, not one, because "did not panic" alone can pass for the wrong
reason:

* it does not panic (the property);
* the same text parses to the same structure twice (so the reader is a function, not a
  side-effecting accumulator — this is what makes the survival evidence rather than luck);
* at least one mutation still produced a parsed function (a positive control, so the test
  cannot pass by the reader refusing everything — the same trap as the export-checker test
  above).

The contract reader (`spec::extract`) reads the same text and is checked for the panic
property too. It survived 300,000 token-soup inputs and 700,000 mutation inputs across the
two entry points while this was being written, so the property appears to hold rather than
merely to be untested. Nothing was found, which is the honest result: a robustness test that
finds nothing has still converted an assumption into a check.

## A number in a document is a claim that must reproduce

The README said "77 of 800 random predicates" were ill-sorted by the old exporter. The
number came from a generator that no longer exists, so no reader could check it. The fix is
`examples/z3diff.rs`, a committed harness whose output the README quotes: 800 and 3000
predicates, 0 parse errors, 0 mismatches with the current printer; 21 of 800 rejected with
the old one. Prefer a number a reader can regenerate to a number that sounds precise.

The harness also had to be checked against itself. Its first version called
`prove(p) == Unsat` a disagreement with z3's `sat`; it is not, because `prove` answers
`Unsat` when `p` is identically false, which is a tautology failure like any counterexample.
111 apparent mismatches were the harness's comparison being wrong. A differential test needs
its own oracle stated explicitly, in a comment, before its output means anything.

## Documentation drifts to describe code that no longer exists

Three README defects in one session, all the same shape: the exporter paragraph described
the *first* fix for the sort bug (the width rule) after the *second* fix replaced it; the
demo output quoted the old `Verdict::Unknown` wording; the layout tree listed `wp.rs` twice
and omitted a test file. Code changes get a test; doc changes get nothing, so docs are where
the previous revision survives.

Two habits help. Quote demo output by *running the example* rather than by remembering it.
And when a fix supersedes a documented behaviour, search the prose for the superseded rule —
`grep` for the phrase the old fix introduced, not for the new one.

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
8. **`blast` must stop on `overflow`, not walk to completion.** Once the node
   table is full every `mk_node` returns `FALSE` without setting `overflow` again,
   so nothing downstream notices. A fold-built term (`pow`, `udiv`) is a fan-out
   DAG whose *unrolled* size is exponential in its step count, and `blast` visits
   a shared subterm once per path to it -- so the walk runs for minutes on a query
   that should have fallen back to SAT. The `overflow` check in `Ctx::blast` turns
   "arena full" into "stop now"; the caller's `overflow` test then routes the query
   to the SAT engine. `overflow` is checked *separately* from `stale`: marking the
   query stale on overflow would refuse it (`Unknown`) instead of falling back.
9. **A fold over a constant must not build the steps that cannot run.** The
   general `pow_fold` gates every step with an `ite`, which is correct and also
   exponential in the unrolled DAG; a literal exponent is known up front, so the
   `smt::const_of` fast path skips the dead steps entirely. The two paths are the
   same recurrence and `a_constant_exponent_agrees_with_a_symbolic_one` pins that
   they agree, because "same recurrence" is an argument and not a measurement.
   Note the symbolic path is still intractable at the BDD wall, so a corpus entry
   with a *symbolic* exponent and a wide base cannot be posed; pin constant
   exponents there.

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

## A construct that cuts a path off is a claim, and vacuous truth is not proof

The recurring shape, now met four times, and worth stating as a rule rather than a story.
Three ways this fragment cuts a path off, each of which makes everything downstream
*vacuously* true — `false => Q` is a theorem for any `Q` — and each of which was, at some
point, reported as a proof:

| the cut | why downstream is vacuous | how it was found |
| --- | --- | --- |
| `Assume(false)` | the assumption is unsatisfiable | hand-built example |
| unreachable `pre` | `pre => wp(body, post)` is a theorem | hand-built example |
| a call to `ensures false` | the callee never returns, so the post-call state is empty | probing the `Call` rule |

All three are now recorded as *failures* (`VacuousAssume`, `VacuousPrecondition`,
`DivergentCall`), because the honest reading is "nothing was proved", not "the contract
holds". The questions to ask, generalising the three above:

* Which statements can cut a path off, and does the report say so when one does?
* When a summary (`verified`, `Total`) is computed, does it distinguish "proved" from
  "proved only because the path was cut"?
* A cut makes the *continuation* vacuous. Does any summary read the continuation without
  noticing the cut? `has_termination_proof` did: `loops == variants == 0` on a program
  whose only divergence was a call.

## A type's invariant must hold for every constructor, including the degenerate input

`Bounded<MIN, MAX>` advertises `LOW <= get() <= HIGH` as an invariant that "cannot be broken
by construction". `new` upheld it; `clamp` returned `MIN` when `MIN > MAX`, so
`Bounded<100, 10>::clamp(50)` gave `100` — outside the type's own range, in the one type the
crate offers as the example of an invariant that holds by construction. Nothing tested the
degenerate range, because every test used a real one.

The question generalises: for a type that claims an invariant, walk every constructor and
every public entry point and ask what the degenerate input does — empty range, zero width,
empty slice, `MIN > MAX`. A refinement type is only as strong as its weakest constructor,
and the degenerate case is where the invariant is usually not even well-defined.

Also: the fix was a signature change (`clamp -> Option<Self>`), not a `debug_assert`. A
`panic` would turn a specification mistake into a runtime abort in the deployed build,
which is the opposite of what this crate is for. When a constructor cannot honour its
invariant, the partiality belongs in its type.

## Probing a rule means probing what it *models*, not what it computes

Both termination findings this session (DEFECT 44's nested-loop havoc, and the
never-returning call) came from the same move: take a rule, ask what program construct it
stands for, and check the model against the construct's real meaning.

* `variant_after` modelled an inner loop as a no-op. Its *computation* was fine; the
  *model* was wrong, and a divergent program was proved `Total`.
* The `Call` rule models "assume `ensures`; continue". That is right for a returning call
  and wrong for one that never returns, and the difference is invisible in the computation.

Neither is reachable by reading the code for arithmetic mistakes. They are reachable by
writing down what each rule claims about the program and asking for a counterexample to the
claim. `examples/` probes are the cheap way to do this; delete them once the finding is
pinned by a test.

## An API surface is a set of claims, and each one has to be walked

The four path-cut findings were all *semantic* — a rule that modelled a construct wrongly.
The findings on the surface are quieter and come from walking each public name and asking
two questions:

* **What does this return, and can the caller silently drop it?** `verify_exhaustive!`
  returned a `bool` while every sibling `verify!` macro panicked, so a false property written
  as a statement ran to completion. A returned `bool` is easy to ignore; a panic is not. When
  a name promises verification, the failure must be unmissable.
* **Does the doc name *every* way the function can fail?** `Fixed::checked_div_int` said
  `None` means `k == 0`, but `i32::MIN / -1` also yields `None`. The function was right; the
  doc named half its failure modes, which is enough for a reader to write the wrong guard.
  The same shape applies to a *type's* constructors: walk every constructor and every entry
  point for the degenerate input (empty range, zero width, `MIN > MAX`).

Both are found by reading the signatures and the doc comments against the behaviour, not by
probing the decision procedure. Worth doing as its own pass once the semantic audit settles,
because the failures are silent by construction — nothing in the test suite is asking the
question.

## A harness that cannot fail is not a harness

Two findings this session, both on *tooling* rather than the engine, and both the same
shape: a check that reports a number while being structurally unable to signal failure.

* `examples/z3diff.rs` collapsed every non-answer from the oracle into one tally. When the
  `z3` Python module was absent from the environment, the harness printed `parse_err=771`
  and exited `0`. So "the exporter printed a file z3 rejects" — the exact bug the harness
  exists to catch — and "the oracle was not installed" were the same output, and neither
  failed the run. Fixing the environment restored the README's `agree=771`, but the harness
  would have reported the same green-looking line had the exporter been broken. The fix
  separates the outcomes (`Verdict` / `ParseFail` / `Error` / `Unavailable`), refuses to run
  without the oracle (exit 2), and fails the run on any mismatch or parse error (exit 1).
* `scripts/test-count.sh` summed lines matching `test result: ok`, so a suite with a failing
  test printed a *smaller* number and exited `0`. A failed run and a smaller passing run were
  indistinguishable, and the number was one this project quotes. The fix makes a failure,
  a compile error, or an empty run a hard error, and prints the count only when the whole run
  is green.

The question to ask of any script or harness in this repo: **can it exit 0 while the thing it
checks is wrong?** If yes, it is not evidence, and quoting its output is a claim, not a
measurement. Teeth for both fixes were run: shadowing the `z3` module (`PYTHONPATH` with a
stub that raises `ImportError`) makes `z3diff` exit 2 with a message; mutating the exporter
(`bvult` -> `bvule`) makes it exit 1 with `mismatch=50`; a deliberately failing test makes
`test-count.sh` exit 1 and name the failure.

## Reading a tool's output is part of the audit

The `parse_err=771` was in the resumed task's own notes as a *passing* figure
(`agree=771`), because the run that produced it had the oracle installed. Re-running the
same command in the resumed environment produced a different, wrong-looking line that was
easy to skim past as "still fine". The lesson: re-run the commands a summary quotes, and
read the *whole* output line — a tally that shifted from `agree` to `parse_err` with the
same total is a silent failure, not a stable result.

## Gates quoted in prose stop being run; make them one command

The gates this crate depends on (clippy `-D warnings`, the test suite, the bare-metal
`no_std` build, the zero-dependency check, the z3, Kani, MIR and Verus oracles) were
separate commands,
written in the README and copied into summaries by hand. That is exactly how a gate quietly
stops being run: the summary says "all gates green" because the four that were re-run were
green, and the fifth was recalled rather than executed. `scripts/gate.sh` is now the single
entry point, it fails on the first gate that does not hold, and it treats an unavailable z3
oracle as a failure rather than a pass.

This is the same lesson as the two tooling defects above, one level up: **a gate you did
not run is not a gate you passed**, and the only way to keep that honest is to make "run
all the gates" a single command whose exit code is the claim. A summary that says "gates
green" should quote that command's output, not a memory of running the pieces.

## A skipped oracle is not a passed oracle: the Ferrocene gate

The crate's whole pitch is the safety-critical corner -- a `no_std`, no-solver prover you
can ship on an MCU. The one piece of that pitch that cannot be self-certified is the
*compiler*: SPARK's story rests on a qualified toolchain, and Rust's is Ferrocene (ISO
26262 ASIL D, IEC 61508 SIL 3, EN 50128, IEC 62304). So `scripts/gate.sh` builds both
crates with Ferrocene for `thumbv7em-none-eabihf` -- a target Ferrocene itself qualifies --
in gate 3, and CI has a matching `ferrocene` job.

Three things had to be true for that gate to be honest, and each is a rule worth keeping:

- **It must not become a dependency.** Ferrocene is invoked as a subprocess through
  `RUSTC=...`, exactly like Kani, Verus, Lean and Coq, so gate 5's zero-external-dependency
  check still passes when it runs. A qualified *toolchain* that leaked into `Cargo.toml`
  would defeat the point of a zero-dependency crate.
- **"Absent" and "failed" must be different exit codes.** `tools/ferrocene/run.sh` exits
  `2` when no toolchain is found and `1` on a real build failure; `gate.sh` skips on `2` and
  fails on anything else. The mirror-image trap is the one gate 10's comment already names:
  conflate them and a broken install reads as "skipped", which reads as green.
- **A skip must be *visible*.** Ferrocene is commercial -- a subscription plus a
  customer-portal token whose archives "don't allow programmatic access" (User Manual
  3.2.1) -- so a public CI job genuinely cannot install it. The gate prints the skip and the
  CI job raises a warning annotation, so "Ferrocene did not run" is on the run summary
  rather than being an absence nobody notices.

The build that carries the weight is `examples/bare_metal.rs`: `#![no_std]`, no `main`, and
it *calls the decision procedure*, so compiling it for the target is what shows the prover
itself is code the qualified compiler accepts. It is a `crate-type = ["lib"]` example with
`test = true`, because the target has no test harness but the verdicts still need checking
somewhere -- the `lib` shape lets the bare-metal build exist, and `test = true` makes
`cargo test --workspace` run the host-side verdict tests rather than building and ignoring
them, which is the "gate that silently did not run" trap again.

What the gate buys is narrow and worth stating plainly: it checks the *qualified compiler
accepts the sources unchanged*. It does not qualify `discharge`. A qualified compiler is not
a qualified verifier, and this crate's decision procedure is outside Ferrocene's scope. The
README's "no qualification evidence" line is still true after this gate runs, and the gate's
comment says so at the definition site.

## An untyped generator is a second program, and it needs its own type discipline

The fuzz generator built random *word* expressions, so every comparison it formed was
8-bit against 8-bit and the query was always well-typed. Adding `truncate` to the grammar
made it able to build `(b < (trunc3(b) << 2))` -- an 8-bit value compared with a 3-bit one --
which the engine *correctly* refuses as ill-formed (`Unknown`). Two existing tests then
failed, and neither failure was an engine bug: the generator had started producing
ill-typed programs that the tests' concrete oracles (`eval`, `evaluate_pred`) cannot be
asked about, because those only have a meaning for a well-sorted term.

The lesson is that a random generator is a second implementation of the language, and it
needs the same type discipline the language does. The fix is two entry points:
`fuzz_expr` (the full grammar, including `truncate`, used only by the word fuzz, which
asserts the weaker "never a wrong `Valid`") and `fuzz_expr_w8` (width-preserving, used
wherever the test compares the term against a concrete value). The refusal path keeps its
own dedicated test. A single generator for both jobs silently moves the well-typedness
burden onto every oracle.

## Mutual recursion between two grammars must decrement on every round trip

Making `ite` reach into the predicate grammar created a cycle: `pfuzz_pred`'s base case
called `fuzz_expr_w8(r, 2)` at a *fixed* depth, while `fuzz_expr_w8(d)` reaches
`pfuzz_pred(d - 1)`. So `pfuzz_pred(1) -> fuzz_expr_w8(2) -> pfuzz_pred(1)` never
terminated and overflowed the stack (found with `RUST_MIN_STACK=33554432`: the test then
passes). The fix threads the incoming depth through the base case, so each round trip loses
one level. When two grammars call each other, the depth has to decrease along the *cycle*,
not just along each grammar's own edges -- a base case that hardcodes a depth is the trap.

## A file tree in the docs is a claim about the filesystem, and nothing checks it

The README's "Layout" section drew `discharge/` as a tree. It had drifted from the
filesystem in three ways at once: `src/lib.rs` was missing, `tests/sym.rs` was missing,
`examples/report_probe.rs` was missing, and the `examples/` and `scripts/` blocks were
*drawn* as if each were the last child of the root (two `└──` siblings), so the tree was
also malformed as a tree. Nothing in the build reads the block, so it stayed wrong across
several commits that each added or renamed a file.

A prose tree is a hand-maintained mirror of `ls`, which is exactly the kind of second copy
that goes stale silently -- the same defect class as a stale test count. The fix here was
manual, but the durable check is one command: extract the names from the block and diff
them against the directories. It caught the last two omissions in seconds. When a document
restates something the code already knows, make the check mechanical or accept that it will
drift; do not fix it by hand and assume it stays fixed.

## `ignore` on a doc example is an example that was never compiled

Two examples in `macros.rs` were marked ```` ```ignore ````: the `contract!` example was
not even valid Rust (it used `x` with no declaration) and the `verify_exhaustive!` example
was a claim about a macro whose whole recent fix was that it must *panic* on a false
property -- the exact property its own unit test checks, written in the docs and never
run. `ignore` is not "this is illustrative"; to `rustdoc` it means "do not check me", so a
doc example marked `ignore` is a sentence that no tool will ever contradict.

Both were made real doctests (the count went 8 passed + 2 ignored -> 10 passed + 0 ignored,
and the gate's test count 247 -> 249). When you write ```` ```ignore ````, ask which
mechanism would notice if the code stopped being true. If the answer is "none", it is not a
doc example, it is prose in a code block.

## A bucket named "agreement" that z3 was never asked to fill

`examples/z3diff.rs` counted three things as agreement: z3 said the same thing, our engine
declined to decide (`Unknown`) on a *well-formed* export, and both sides declined on an
ill-formed one. The first is real agreement. The third has its own counter already and is
different in kind: the export carries no `(check-sat)`, so there is no query to send. The
second is the one that was mislabelled: the export was well formed and z3 was never
invoked, so the case reached one party, not two. Folding it into `agree` means the summary
reports agreement for cases the oracle never saw.

Measured before changing anything: the bucket was 0 at both 800 and 3000 predicates, so the
quoted numbers were not wrong -- they were only *accidentally* right, on the strength of the
generator happening never to emit a well-formed-but-undecided case. The defect is that
nothing distinguished "z3 agreed" from "z3 was not asked"; the correct count depended on a
property of the input distribution rather than on the code.

Split into a separate `undecided` counter, reported in the summary line, with the reasoning
in the comment. The README's measured line now carries it too. This is the same class as the
rest of the crate's findings: a summary that can outrun the run it summarizes. When you
write `agree += 1`, name the two things that agreed; if one of them was never asked, it is
not agreement.

## A documented direction the generator never generated

The README said `examples/z3diff.rs` covers "`truncate` in both directions". The generator's
`truncate` arm was `truncate(x, 1 + r.below(w))`, and `below(w)` is in `0..w-1`, so the result
width was always `1..=w` -- always *narrowing*. `truncate` accepts a width above the source
(it is a zero-extend), and the exporter's `zero_extend` branch is the one that used to be a bug
(`((_ extract 15 0) x0_8)` on an 8-bit vector, ill-sorted and rejected by z3). So the harness
advertised the direction that exercises the fragile printer path and never generated it. The
printer branch was covered by a unit test asserting the text, but never by the oracle that exists
to catch exactly this: a claim about what was tested that the test did not test.

Fix: a widening arm that pairs `truncate(x, wide)` with a narrowing `truncate(.., w)`. The pair
matters -- a bare widening leaves the result wider than `w`, and every other operation in the
generator is width-preserving, so the predicates would compare mismatched widths, the term would be
refused, and the case would never reach z3. Pairing keeps the width at `w` while putting both
printer branches in one tree.

Verified by instrumentation, not by inference: a temporary counter for `zero_extend` in the
exported text reported 35 of 800 files, all accepted by z3 (0 parse errors). Without that check
"agree went up" would only have meant the generator produced *something* different; it would not
have shown the intended branch was reached. The counter was removed before committing; the
generator change is the only diff.

Numbers moved (both re-measured): 800 predicates refused 29 -> 25, agree 771 -> 775; 3000 refused
108 -> 97, agree 2892 -> 2903; mismatch 0 throughout. The README's measured line was updated.

Lesson: when a comment or README enumerates what a generator covers, check the generator against
the enumeration one item at a time. "Covers X in both directions" is a claim about a distribution,
and a distribution can be narrower than its description without any single run looking wrong.

## An assertion that compared a term with itself

`truncate` is the crate's only width-changing operation, so the tests around it matter. Three of
them contained the same defect: an `assert!(prove(eq(t, <the call that defines t>)))`.

- `tests/differential.rs`, `widening_through_truncate_agrees_with_the_original_value`:
  `t = truncate(x, dst)` then `prove(eq(t, truncate(x, dst)))`. Both sides are the same term
  id, so the equality is a tautology and the assert can never fail -- under a comment that said
  it checked the widened value "matches the original".
- `tests/quant.rs`, `truncate_keeps_the_low_bits_and_zero_fills`: `low = truncate(x, 2)` then
  `prove(eq(low, truncate(x, 2)))`, and `wide = truncate(x, 8)` then
  `prove(eq(wide, truncate(x, 8)))`. Same shape, twice.

Because the terms are hash-consed, the two sides are literally the same node, so the obligation is
`eq(v, v)`, which the engine returns `Valid` for without ever touching the bit-blaster. The tests
were green and proved nothing about truncation. Note the third case in that same test,
`truncation_through_an_assignment_survives_substitution`, is *not* this defect: it compares
`after = substitute_word(narrowed, [(x, y)])` against `truncate(y, 2)`, and `after` and that call
are different nodes, so the check is real. The shape "compare `t` with a call that mentions `x`" is
fine; the shape "compare `t` with the call `t` is bound to" is vacuous.

Fix: pin the input with `prove_implies(eq_const(x, 0b1011), eq_const(t, <expected>))`, which makes
the claim falsifiable. For the widening round trip, `prove(eq(truncate(t, src), x))` -- narrow the
widened value back to `src` and require the original, which is well sorted (both sides `src` bits)
and is the non-trivial form of "widening preserves the value".

Verified by mutation, not by reading: flipping the bit-blaster's widening zero-fill from `FALSE`
to `TRUE` (`src/smt.rs`, `Op::Trunc`) makes both fixed tests fail, reporting counterexample
`x = 11`. Before the fix the same mutation left them green -- which is the whole point: an
assertion that cannot fail also cannot detect the bug it was written for. Source restored after.

Lesson: a test of an operation must compare the result against something *other than the
expression that produced it*. When the operands are hash-consed, `eq(t, f(x))` where `t == f(x)` is
not a weak test, it is no test. Pin an input, or compare against an independently computed value.

## A sentinel that was the first real variable

`wp.rs` had a comment on `writes` that read: "Slot 0 is never a real variable: `var()` starts
indices at 0, but a sentinel is all the initialisation needs". The buffer it describes is
`[Var::SENTINEL; MAX_WRITES]`, and `Var::SENTINEL` was `Var(Term(0))`. The term arena allocated ids
from 0, so `Term(0)` was the *first real term*, and `Var::SENTINEL == var(8)` was true. The
comment said the opposite of what the code did.

It was latent: every reader of those buffers is `[..n]`-counted, and no code compares a handle
against `SENTINEL` by value, so nothing was wrong at runtime. But the frame rule's whole design
leans on the sentinel being distinguishable from a live handle -- `MAX_WRITES` fixed buffers,
`out[..n]`-counted reads, no allocator -- and the one line a reviewer would check to confirm that
assumption was false. An invariant that is false and untested is a landmine for the next change
that does compare, or for anyone who trusts the comment.

Found by reading `SENTINEL`'s definition against `mk_term`, then confirmed by probe: a temporary
example printed `var(8) == SENTINEL ? true`. The fix is to make the claim true rather than delete
it: reserve term id 0 (`smt::TERM_SENTINEL`), start `n_terms` at 1 in both `Ctx::new` and `reset`,
and point `SENTINEL` at it. Cost is one term out of `CAP`. A regression test,
`the_sentinel_is_not_a_real_variable`, asserts `var(8) != Var::SENTINEL` -- it failed before the
fix and passes after, so it is not a comment about the fix.

Note the same `Term(0)` also appears as the *overflow* return in `mk_term`, `var_term`, and
`subst`. Those are deliberate: they poison the handle and set `overflow`/`stale`, and `prove`
checks the flag before answering, so a bogus `Term(0)` never reaches a verdict -- `smoke.rs`
documents measuring exactly that. Reserving id 0 leaves those paths alone; they return the reserved
id, which is still not a valid node, and the flag is still what refuses the query.

Lesson: when a comment asserts an invariant ("slot 0 is never a real variable"), it is a claim
like any other and deserves a test. If the invariant is load-bearing, make it true and pin it;
deleting the comment would have hidden a real coupling between `wp`'s buffers and the arena's id
allocation.

## A differential oracle that could not see a wrong operator

`examples/z3diff.rs` generates random predicates, exports them, and asks z3. It was passing at
`mismatch=0`, so it looked like the exporter was checked. It was not, in the way that mattered.

The harness compares only sat/unsat. A random predicate over free variables is essentially never a
tautology, so a *semantic* printing bug that keeps the formula well sorted is invisible: I changed
the exporter's `Op::Sub` to print `bvadd` instead of `bvsub`, and the random sweep still reported
`mismatch=0`. A probe showed `bvsub` in 39 of the 800 exports, every one decided -- so the operator
was exercised on every run and never *checked*. An instrument that is present in the sample but not
load-bearing in the assertion is the same defect class as the `Var::SENTINEL` comment: it looks
like coverage and is not.

Why it is invisible: the export asserts `(not p)`, so z3 answers `unsat` exactly when the printed
`p` is a tautology. For a random `p` z3 answers `sat` both before and after any semantic change that
preserves satisfiability, and swapping `bvsub` for `bvadd` does. The only predicate shape that
distinguishes the two is a *tautology*, and the generator makes almost none.

The fix is the dual of the random sweep: a corpus of tautologies by construction, one or more per
operator, each chosen so that a plausible mutation of the operator it names breaks the identity.
`sub.self` (`x - x == 0`) is sensitive to `bvsub`→`bvadd`; `mul.one` (`x * 1 == x`) to
`bvmul`→`bvadd` (note `add.comm` would not be -- commutativity survives the swap, so the identity
has to be picked against the mutation, not just to mention the operator); `shl.nibble`
(`0x0f << 4 == 0xf0`) to a shift-direction swap; `trunc.widen` to `zero_extend`→`sign_extend`.
42 identities across 8- and 12-bit widths, printed with the same `Query` path the random sweep uses.

Teeth, measured by mutating the printer and requiring the harness to fail: `bvsub`→`bvadd`,
`bvmul`→`bvadd`, `bvand`→`bvor`, `bvshl`→`bvlshr`, `bvxor`→`bvor`, and widening
`zero_extend`→`sign_extend` each now exit 1 with the failing identity named. Before the corpus, the
first of those passed silently.

Lesson: a differential test's *generator* determines what it can catch, and "the operator appears
in the output" is not "the operator was checked". When a decision is sat/unsat, the discriminating
inputs are the degenerate ones -- tautologies and contradictions -- not the generic ones. If you
want to know whether a check has teeth, mutate the thing it is supposed to check and confirm it
fails; if it does not, the sample was decorative.

## Completeness guards that nothing exercised

`wp::writes` derives a statement's write set into a fixed `Frame` of `MAX_WRITES = 16`
variables and sets `complete = false` when a body writes more. Five places consult that flag,
and the crate's own comments assert each is load-bearing -- the one in `variant_after` even
documents the divergence it prevents. Mutation testing said otherwise: blanking two of the five
guards to `if false` left the whole suite green.

1. `Stmt::frame` returns `false` for an incomplete *derived* frame. Its doc says
   `under_declaring_the_frame_is_rejected` covers this. It does not: that test builds a
   2-write body, so the frame is complete and the guard never runs; the test exercises the
   *declared-covers-derived* check, a different guard two lines down. A body writing 17
   variables is where the completeness guard is the only thing standing -- without it,
   "declared covers derived" is checked against a 16-entry prefix and a caller who declares
   those 16 passes while the callee overwrites the 17th.

2. `collect_written`'s `Call` arm propagates the callee's incompleteness upward. A caller that
   merely *calls* an over-cap callee directly writes one variable, so its own frame looks
   complete without the propagation, and the enclosing check accepts a prefix again -- the same
   hole one level up.

Both are now pinned by tests that fail when the guard is removed: build a 17-write body, check
the derived frame is `len() == 16 && !complete()`, and assert `frame` refuses / the caller's
frame is incomplete. The verdict the *program* gets is refuted either way, so the test has to
assert on the guard's own observable -- `complete()`, or the refusal -- not on a proof failing.
That is the same lesson as the z3 identity corpus: a guard is only tested if the test observes
the thing the guard controls, and "this program does not verify" can be true for several
reasons at once. When a comment claims a named test covers a branch, read the test and check it
reaches the branch; here the comment was aspirational.

Method note: I found these by mutating each `if !…complete()` to `if false` and running the
suite, not by reading. Reading confirms a guard is *present*; only mutation shows it is
*load-bearing*. Both surviving mutants sat behind comments claiming coverage, which is exactly
where reading is least reliable.

## The assertion arm was the last silent `push`

The obligation cap was fixed once before (commit c786848): claim-carrying obligations went
through `push_checked` and raised `ObligationOverflow`, but the `Stmt::Assert` arm was left on
the old silent `push`, deliberately, with the argument that a dropped assertion is harmless
because the backward walk still conjoins it into the weakest precondition. That argument is
correct about `verify`'s soundness and wrong about `wp::obligations`: the latter documents its
third return value as `true` only when every side obligation is in the buffer, and it returned
`true` for 17..=20 assertions when the buffer holds 16. Two answers to one question, which is
the exact defect the earlier fix existed to remove.

The gap survived the earlier fix because every existing overflow test used *loops*, not
assertions -- the pressure family pads with assertions but asserts only on `verify`, never on
`obligations`' completeness flag, so the flag's assertion case was never observed. Found by
probe, not by reading: `obligations()` with N assertions for N in {15,16,17,20}.

Fix: `Stmt::Assert` now goes through `push_checked`; `push` is deleted (no callers left).
`verify` on a truncated assertion set now reports `ObligationOverflow`, and the completeness
flag goes false. Pinned by `assertions_beyond_the_cap_are_reported_not_hidden` in `tests/wp.rs`,
which fails when the arm is reverted to a silent drop. Lesson, same as the frame guards: when a
comment justifies leaving one site different from its siblings, test that site's own observable
-- here the completeness flag -- not the end-to-end verdict, which stays correct for the wrong
reason.

## The Kani oracle: a second verifier, and the bugs building it exposed

`examples/kanidiff.rs` checks the engine against Kani (model checking over CBMC), the same
way `z3diff` checks the exporter against z3: Kani is a subprocess oracle, never a
dependency. The predicate and the Rust text it compiles are two interpretations of one
shared IR tree, not independently generated -- otherwise "the same property" is a hope.

Building it found three bugs, all in the harness, each of which would have made a green run
mean less than it looked:

1. **Arena sharing.** One `with_fresh` for all cases exhausted the node budget after ~a
   dozen queries, so later cases came back `Unknown` and the harness reported the engine as
   weak (`not_proved=27`). The engine was fine; the harness had run the arena dry. Each case
   now gets its own arena.
2. **Shift semantics.** The engine defines a shift by `k >= width` to be 0 / sign bit
   (SMT-LIB rule); Rust `<<`/`>>` are an arithmetic-overflow error there. Emitting `x << k`
   would have compared a different function. The generated crate now spells the engine's
   rule out in `shl_eng`/`lshr_eng`/`ashr_eng`.
3. **The classification matrix.** The first version counted "engine refuted + Kani proved"
   as agreement. A mutated `Sub` blast then produced `mismatch=0` on the random sweep and
   was caught only by the curated corpus. Now only `Unknown` is "no claim"; any other
   engine verdict is a definite claim Kani must not contradict. Found by mutating the
   engine, not by reading.

Two corpus entries were also wrong (a bare `Not(And(..))` is not De Morgan; `guard <=>
ite(guard,a,b)==a` fails at `a==b`), which the engine correctly refuted. Lesson that keeps
recurring: when the harness disagrees, suspect the harness first, but *check* -- here the
engine was right both times.

Mutation evidence the harness has teeth: `Sub`'s `borrow = TRUE` -> `FALSE` makes the engine
refuse `sub_self`/`add_sub_cancel`/`sub_zero`; `Eq`'s per-bit `and` -> `or` makes it prove
false formulas, caught by the random sweep. Negative control `a - b == b - a` fails the run
if either side proves it.

## Verus as a third oracle

`examples/verusdiff.rs` checks the engine against Verus the way `kanidiff` checks it against
Kani. Both harnesses now take their cases and IR from `examples/support/mod.rs`, so they
check the *same* formulas; giving each its own corpus would make the two agreement claims
disjoint. Three backends (the engine, Kani, Verus) on different foundations means a blasting
bug has to survive agreement with both verifiers.

Verus facts that cost time to find, all in the generated-file path:

* `#[verifier(bit_vector)]` is required or Verus uses non-linear arithmetic and fails on
  bitwise facts. With it, `+ - *` on `u8` wrap.
* `wrapping_mul(x, 1u8)` is *rejected* in `bit_vector` mode: "expected finite-width integer
  in `bit_vector` proof, got Int(Nat)". Route arithmetic through spec helpers
  (`(x * y) as u8`) instead.
* A constant expression that overflows, e.g. `255u8 * 255u8`, is a rustc const-eval *error*
  that aborts the whole run -- `#![allow(arithmetic_overflow)]` does not help. The spec-helper
  form avoids it because operands are already `int`.
* `verification results:: N verified, M errors` counts non-case items (`main`, helpers), so
  `verified + errors == cases.len()` is false. Account on error *locations* mapping to cases,
  and fail on any error that maps to none.
* Install: download the `x86-linux` release zip (self-contained, own `z3`), extract, chmod +x
  `verus`/`rust_verify`/`z3`, then `rustup install <the pinned toolchain verus --version
  prints>`. Point `VERUS_BIN` at the driver.

## GitHub Actions

`.github/workflows/ci.yml` has three jobs. The first runs `scripts/gate.sh` verbatim, so CI and
a local run mean the same thing. The other two install Kani (cached) and Verus (latest
release) and run `kanidiff` and `verusdiff` as hard gates. `gate.sh`'s Kani and Verus steps
skip when those tools are absent -- reported, not silent -- because both are large downloads;
CI is where they become mandatory. Gate count is now 8 (the MIR frontend is the eighth).

Three things about this file are easy to get wrong:

1. **Pin every `uses:` to a full commit SHA, with the tag in a trailing comment.** A tag is
   movable, so `@v4` lets a retagged or compromised release change what CI runs without any
   commit in this repository changing. The comment matters too: a bare SHA does not tell a
   reviewer which version it is, and a pin they cannot identify is a pin they cannot check.
   Resolve a tag to its commit with
   `curl -s https://api.github.com/repos/OWNER/REPO/git/ref/tags/TAG` -- for these actions the
   tag is lightweight, so `object.sha` is the commit directly. Verify it before trusting it.
2. **A workflow added by a pull request does not run on that pull request.** GitHub only
   starts `pull_request` runs when the workflow file already exists on the *base* branch, so a
   PR that introduces `.github/workflows/ci.yml` shows "no checks reported" until it is merged.
   That is expected, not a broken pipeline: it is why the local `gate.sh` run is the evidence
   for such a PR, and why the workflow says so rather than looking untested.
3. **`gh` needs `read:org` for some queries, a classic token may not have it.** `gh pr edit`
   fails with "The 'login' field requires one of the following scopes: ['read:org']" on a token
   scoped to `repo` only. The REST API does not need that scope, so update the PR body with
   `curl -X PATCH .../pulls/N -d @payload.json` instead of reaching for a broader token.


## A fallback engine is only worth its weight if the wall actually moves

`smt.rs` is a BDD engine; when its arena fills, `query_valid`/`query_model` hand the *same*
term graph to `sat.rs`, a CDCL SAT solver, via `bitblast.rs`.

Two engines, one term graph, **two blasters** -- and the distinction matters, because the
first write-up of this said "one netlist" and that was wrong. `smt::blast` writes BDD node
ids; `bitblast::blast` writes `Lit`s. They cannot be one function: the term arena and the
gate arena are both `&mut`, so a shared blaster would have to split an arena or hide a
pointer behind a trait. What the two share is the *term graph*, so each operation is named
once -- operands and width are decided when the node is built -- but each blaster writes its
own adder, subtractor, multiplier and comparator circuit. So "the arithmetic is defined once"
is itself too strong: the *operations* are defined once, the *circuits* are not, and the two
circuits could diverge. That is a real risk, so it is treated as a property to check rather
than hope away. "One bit-slicer" and "one netlist" are both the stronger, false version of
this; the code and `src/sat.rs`'s header say the true one.

### The check has to be aimed at the blaster it is about

The first fix for the wording above kept the sentence "if the two adders ever disagree, one
of those fails", naming `tests/differential.rs` and the z3 oracle. That was measured and it
is **false**. Both run at widths where the BDD engine finishes (the z3 corpus sweeps 8 and 12
bits; the differential corpus pins every op at 1--4 bits *precisely so the BDD can finish*),
so every query they make is decided by `smt::blast`. `bitblast::blast` only runs once the BDD
arena has already filled, which is 64 bits for an adder and 8 for a multiplier -- nothing in
the suite reaches it.

The measurement: delete the carry-generate term (`a & b`) from `bitblast.rs`'s adder so it
computes `xor`, and drop a carry term from its multiplier. Then run the lot. `cargo test`
passes, `tests/differential.rs` passes, the z3 oracle reports `mismatch=0`, and the probe
still prints `add_comm 64b valid`. A query that *does* force the SAT path and is sensitive to
the bug (`add(x, y) == xor(x, y)`, or `(x+y)-x == y` at 64 bits) comes back `Valid` and
`Counterexample` -- that is, an unsound proof and a spurious witness, from a suite that is
green.

The fix is the `tests` module in `bitblast.rs`: drive `blast` directly, force both inputs,
and ask the solver whether the circuit can differ from Rust's wrapping arithmetic, exhaustive
over every input pair at 1--4 bits. It catches both mutants, and its own teeth are checked
(the helper is made to answer "no divergence" unconditionally and the teeth test fails). The
lesson is not "add a differential test"; it is that a differential test *between two engines*
proves nothing about the engine that never runs. The oracle has to reach the code under test,
and the way to know it does is to break that code and watch the test fail.

The point of recording this here is the measurement discipline, because the first version
of this feature *claimed* to have broken the wall and had not.

1. **An unsound solver reports a "better" result than the truth.** The first SAT engine
   answered `Valid` on queries the BDD engine could not decide. That looked like the wall
   breaking. It was a bug: the watch-list arena was one shared array with per-literal
   *counts* but no per-literal *offsets*, so two literals' watch lists overlapped, unit
   propagation was missed, and the solver called unsatisfiable formulas satisfiable. The
   "success" and the unsoundness were the same event. Differential tests against
   brute-force enumeration (`tests/sat_engine.rs`) are what separated them.

2. **The wall is where `Unknown` appears, and it is printed, not remembered.** After the
   solver was made sound the wall came back. Run `cargo run --release --features std
   --example probe` for the table. The honest result: adder equivalence now settles at 64
   bits (`Unknown` with the fallback disabled, `Valid` with it); wide *multiplier*
   equivalence is out of reach at both engines' budgets.

3. **Tombstoning is not deletion.** `reduce_db` marked dead learnt clauses with `c_len = 0`
   but left their ids in the occurrence lists, whose spans were sized for the pre-deletion
   clause set. `propagate` then walked a stale span and could report a conflict that did not
   exist. If a clause is removed from a list, remove it from every list that indexes it, or
   rebuild them.

4. **Learnt clauses that are never freed are a memory leak with a proof-theoretic cost.**
   The literal arena filled with worthless learnt clauses, so a query the solver could still
   decide came back `Unknown` for lack of space. `reduce_db` now keeps a set (originals,
   current reasons, the more active half of the rest) and `compact` re-lays the arena,
   remapping `reason` and rebuilding the occurrence lists. `SOLVER_BYTES` is
   `size_of::<Solver>()` for this reason -- the hand-summed version went stale the moment
   the new fields landed.

5. **An incomplete engine needs a budget, not patience.** `MAX_CONFLICTS` bounds the search;
   past it the solver returns `Sat::Unknown`. A verifier that hangs is worse than one that
   declines. The budget is also the honest knob: 20 000 conflicts cannot decide 64-bit
   adder equivalence, 50 000 can, and `MAX_CONFLICTS` records which side of that line the
   crate commits to.

The pattern is the one the rest of this file keeps finding: a claim about the engine is
worth only the command that measures it, and a *better-looking* claim is the first thing to
suspect.

## A verdict is a fact about a query; whether it is *good* depends on the query

The frontend turns each source obligation into an SMT query, and the two commonest
obligations ask *opposite* questions:

* A postcondition asks "does `path => post` hold for every input". `Valid` is the proof;
  `Unsat` means the postcondition is false on **every** input, which is the strongest
  possible failure.
* A panic (and an `unreachable`) asks "can this happen". `Unsat` is the proof;
  `Counterexample` is the failing input; `Valid` means it happens on **every** input,
  which is the worst case and has no witness to show.

The first version tested `verdict.is_proved()` — that is, `Valid` — for every obligation
regardless of kind. That reads the panic polarity backwards: a panic that fires on every
input is reported as *ruled out*. It also silently accepted the `Unsat` postcondition,
because `Unsat` is not `Valid` but the outcome classifier only looked for a
`Counterexample` and let everything else fall through to `Verified`. Both are the same
mistake — treating "the engine decided" as "the engine approved" — and both make the
crate's core claim (a `Verified` line means the obligations hold) false.

The fix is [`Obligation::is_discharged`], which is per-kind on purpose, and a
[`MirReport::first_failure`] that carries a witness *or* the "holds for every input" case
so an obligation with no counterexample is still a failure. The regression targets are
`bool_ret_false` (postcondition `Unsat`), `vacuous_precondition` (unsatisfiable `requires`),
and `div_by_always_zero` (panic query `Valid`). Each was checked by reverting the fix and
watching it fail — a test for a polarity bug that passes on the buggy polarity is not a
test.
### The same mistake in a boolean, and in a failure string

Two follow-on findings were the same error in different clothes, and both are worth naming
because they are easy to reintroduce.

1. **A satisfiability query has three outcomes, and a `bool` cannot hold three.**
   `find_model` returns a model, `Unsat`, or `Unknown`. The first
   `Contract::precondition_is_satisfiable` was `find_model(pre) != Verdict::Unsat`, which
   folds `Unknown` in with "found a model" and answers `true`. An ill-formed precondition
   (an equality between an 8-bit and a 16-bit variable, say) then reads as *satisfiable*,
   so a caller checking `discharge` and the boolean together claims a non-vacuous proof
   with no evidence the precondition is reachable. The fix adds
   `Contract::precondition_satisfiability`, returning the verdict, and makes the boolean
   `true` only for `Valid` or a `Counterexample` -- the two outcomes that *are* a satisfying
   input. `false` now means "not established", covering both `Unsat` and `Unknown`, and the
   docs say so. The rule from above applies: three outcomes need a three-valued type, not a
   boolean with a silent fold.

2. **Two failures with no witness are not the same failure.** `first_failure` returned a
   kind and an optional witness, and the caller rendered "no witness" as the string "holds
   for every input". That string is right for a `Valid` panic query (the panic fires on all
   inputs) and exactly *backwards* for an `Unsat` postcondition (the postcondition holds
   for **no** input). The detail is now built per kind and per verdict by
   `Obligation::failure_detail`, and `first_failure` returns the obligation itself so the
   kind, the witness, and the diagnosis come from one place instead of being re-derived.
   The regression test asserts the `Unsat` postcondition's detail says "no input" and does
   *not* contain "holds for every input".

The through-line with the polarity bug: a value that can mean two opposite things, rendered
or tested without its direction, will eventually be read the wrong way.

## A guard can be load-bearing and still invisible to a verdict

The second oracle of the same shape as "a harness covers only what it reaches", and the
sharper one, because the code *is* reached. `Solver::reduce_db` runs at every 2000
conflicts, and a 64-bit adder equivalence crosses that interval 15 times, so nothing here is
dead code. Yet deleting the loop that marks every clause currently justifying a trail
literal as `keep` left the entire suite green -- `cargo test`, `tests/sat_engine.rs`,
`tests/differential.rs`, the z3 corpus, and the Kani oracle.

The reason a verdict-level test cannot see it is the point. Dropping a reason does not
usually change the answer: `compact` remaps `reason[v]` to `NO_CLAUSE`, the literal becomes
indistinguishable from a decision, and `analyze` stops early and learns a *weaker* clause.
The solver still finds the right verdict, just more slowly. Instrumenting the guard showed
it rescuing 650 clause-reasons across those 15 calls, and with the guard removed 426 trail
assignments lost their justification while the verdict stayed `Unsat`. Correct verdict,
corrupt proof state.

So the oracle has to assert the invariant, not the outcome: each decision level holds
exactly one reason-free literal, at the front. That check fails on the mutant at level 4,
which is the only evidence the teeth are real. And it drives `reduce_db` on a hand-built
trail rather than searching for a hard instance, because a test that needs a 2000-conflict
search is a test that runs in minutes and whose teeth depend on the search happening to
reach the guard. Build the state the guard protects, then remove the guard and watch the
assertion fire.

Two mechanical notes worth keeping. A `Solver` is 2.2 MB, so a fixture that owns one
overflows the 2 MB test-thread stack -- use the shared static, and take the lock's
`MutexGuard`. And with every clause at the same activity, `reduce_db`'s stable sort keeps
the low ids, so the guard looks unnecessary by accident; set the activities explicitly so
the removable clauses really are the ones that get removed.

## A test that skips itself still reports `ok`

The sharpest instance of the "a harness covers only what it reaches" rule, because nothing
here was dead or wrong. `Obligation::is_discharged` in `src/mir/exec.rs` decides whether an
obligation is discharged, and the answer is *per kind*: an `Unsat` verdict **discharges** a
panic query ("it cannot happen") and **refutes** a postcondition ("it holds for no input").
Collapsing that match into `self.verdict.is_proved()` is the natural single-polarity reading,
and it is a soundness hole in both directions at once.

That mutant survives `cargo test` completely. The reason is not that the logic is unreached;
it is that the only tests for it live in `tests/mir.rs`, which needs `DISCHARGE_RUSTC`
pointing at a nightly, and **skips itself when it is absent** with a bare
`let Some(report) = verify_all() else { return };`. A skipped test reports `ok`. So the suite
count is *identical* whether the MIR frontend ran or not: 325 with the nightly, 325 without.
CI never set `DISCHARGE_RUSTC`, so in the one place that gates a merge, the polarity had no
teeth at all. A green suite said nothing about it.

Two fixes, and both are needed. First, an in-module oracle in `src/mir/exec.rs` that runs
*ungated*: it enumerates the whole truth table over the four kinds and four verdicts, so it
does not need a compiler or a model -- `Valid`, `Unsat` and `Unknown` are unit variants, and
a real `Cex` comes from `find_model` on a satisfiable-but-not-valid query. Verified by
mutation: collapsing the match, treating a `Valid` panic as ruled out, and discharging every
vacuity check each fail the oracle on a stable-only machine. Second, CI now installs the
nightly and points `DISCHARGE_RUSTC` at it, so the end-to-end tests actually run. That
variable must be a *path*, not a toolchain name: the frontend runs it with `Command::new`.

The lesson to carry: a test that can silently become a no-op is not a test. When a harness
skips on a missing tool, the count that "proves" the suite is green has to be checked
against the count with the tool present. If the two are equal, the tool is not being used.

## Pin a remap by what it points at, not by where it points

A related trap in the same style, from the `reduce_db` oracle. `compact` renumbers clauses,
so it remaps `reason[v]` from the old id to the new one. The first version of the oracle
asserted only `reason[v] < n_clauses` -- "the reason names a live clause". That check passes
for *any* surviving clause, including one that has nothing to do with the literal it is
supposed to justify, so a remap that pointed every reason at clause 0 would have slipped
through. The oracle now compares the clause's literal *set* against the expected one, and a
mutant that remaps reasons to an unrelated live clause fails it.

The same fixture had a second hole worth naming. It left each reason clause's other literal
unassigned, so `clause_justifies` was never really exercised: the clause could not be shown
to be unit. The fixture now decides the other literal, so the reason clause is genuinely unit
on the propagated literal -- `(x2 | ¬x6)` with `x6` true -- which is what makes it a real
propagation justification rather than a clause that merely mentions the variable.

## An arena budget is not a time budget

The MIR frontend hung. `count_evens` -- `while i < n { if i % 2 == 0 { c += 1; } i += 1; }`
with `requires: n <= 8` -- ran for minutes and printed nothing, so the tool reported *no
verdict at all*, which is worse than any verdict. The first three explanations were wrong,
and each one was falsified by measurement rather than by reading:

1. **"The open-addressing tables filled up."** Plausible: `mk_node`, `mk_term`, and the
   three `apply2` caches probe with `i = (i + 1) & mask` and no termination test, and the
   capacity check sits *inside* the `k == u64::MAX` branch -- so a table with no empty slot
   left can never reach it. That is a real latent bug and it is fixed, but it was not this
   hang: instrumentation showed `overflow == false` and `nodes == 53` at 24 million
   `apply2` calls.
2. **"The BDD blew up."** Also plausible, and also wrong: 24M calls producing 53 nodes is
   the signature of recomputation, not of a growing diagram.
3. **"It is in `apply2`."** Wrong: instrumenting `apply2`, `blast_bool`, and `model` showed
   `model()` completing in 7 iterations, then silence.

What found it was printing the frontend's own state. The worklist was visiting `bb1`..`bb7`
in a cycle forever, with `visits` growing by one per round. So it was not an infinite loop
and not a deadlock: it was a **path explosion**, slow enough to look like a hang. Every
branch inside an unwound loop multiplies the path count, and each path's BDD is larger than
the last, so the cost is super-linear in the path count. Measured: 200 paths took 16s, 2000
paths were still running after 90s.

The fix is `DEFAULT_PATH_BUDGET` in `src/mir/exec.rs`. `DEFAULT_UNWIND` bounds each loop;
nothing bounded the *number of paths*, and that is the missing guard. It is set to 64
because the measurement says a larger value buys no coverage -- the corpus scoreboard is
4 of 14 at 64 paths and 4 of 14 with no bound at all -- only latency.

Two lessons. First, **a bound on one resource is not a bound on the others**: this engine
had an arena budget and a loop budget, and still had no termination guarantee. When a tool
promises "never loop forever", that promise needs a guard on *time* or *steps*, not just on
memory. Second, **instrument before you theorise**. Three plausible root causes were wrong
here; the one that was right came from printing the loop's own counters, not from reasoning
about which data structure "must" be the problem.

The regression test is `a_branching_loop_reports_a_path_budget_rather_than_running_forever`
in `src/mir/exec.rs`. It embeds the real `rustc -O` MIR for `count_evens` so it runs on
stable, and it is *verified to hang without the fix* -- which is the only thing that makes
it a regression test rather than a test that happens to pass. Two details matter: it must go
through `verify_function` with a postcondition, because the postcondition is what makes each
path cost more than the last; and it runs on a 64 MB thread, because the harness's default
stack is smaller than the main thread's and the workload overflows it.

## Cutting a loop at its invariant: the header must havoc what the loop writes

Loop invariants landed in the MIR frontend, and the first version was **unsound**. It
verified a postcondition that is false. This is worth recording in full, because the
mistake is the natural one and the symptom is a *success*.

The shape was the obvious one for a CFG. On every edge into the loop header, assert the
invariant; on an edge from a back edge, assert it and stop rather than re-enter. That
closes the induction with no unwinding: the assertion at the back edge is the step, the
assertion on the entry edge is the base case. Measured, it worked -- `count_evens` went
from *path budget exhausted* in 2.8 s to *verified* in 0.06 s, and the realistic corpus
went from 4 of 14 decided to 7 of 14.

It was wrong. `sum_to` with the deliberately weakened invariant `i <= n` -- which is true
on entry and preserved, but says nothing relating the accumulator to the counter -- came
back **verified**, while the loop plainly returns a value that violates `ret <= 8` for
`n = 8`. The tool had proved a false statement.

The cause is what the exit edge carries. `advance` asserted the invariant and then
continued into the header with the path the path *arrived* with. For the entry edge that
is the pre-loop state, so the guard is evaluated there: `0 < n` gives `n >= 1`, and
`!(0 < n)` gives `n == 0` with the counter still `0`. The exit edge is therefore only
ever walked from the state of the *first* iteration. Everything the loop does on its
second pass and later -- including writing the return value -- was never seen. A proof
that only inspects the first iteration is not a proof of the loop.

The fix is the standard rule, and it is a rule precisely because this is the trap. At the
header, **havoc** the locals the loop can write -- replace each with a fresh variable --
and only then assume the invariant. What the exit edge carries is then `I && !guard` over
*arbitrary* values satisfying `I`, which is what the invariant is a claim about. The
`havoc` set is an over-approximation (reachability from the header over the whole
function), which is the safe direction: havocing a local the loop never writes loses
information and can turn a proof into an open obligation, never the reverse. `_0`, the
return place, must be in the set; leaving it out is the specific way the hole reappeared,
since `s` in `sum_to` *is* `_0`.

Two things made this findable rather than a silent false positive:

* **A mutation test, not a reading.** The weakened invariant was checked by hand against
  the corpus before being trusted. Reading the `advance` code did not reveal the bug; the
  two-word diff that changed `s == i` to `s == 0`-equivalent did.
* **A regression test that fails without the fix.** `an_invariant_too_weak_for_the_
  postcondition_is_not_a_proof` asserts only "not verified" -- a counterexample or an open
  obligation both satisfy it -- and it was confirmed to *pass* on the unsound version and
  fail once havoc was disabled with `if true { continue; }`. A test written after the fix
  that only pins the happy path would have missed this entirely.

A smaller trap sits next to it. Classifying the edges needs care: the block *before* the
header also jumps into it, and that edge is the entry, not the latch. The test that gets
this right is `to <= from` -- strictly earlier targets are the entry, equal-or-later ones
are the latch, and a header that loops to itself is a latch. A "cleaner" two-pass version
that collected every block edging into the header from later in the layout classified the
entry edge as a latch, cut the loop before it was entered, and reported a proof of a false
postcondition again. The mutation tests caught it in seconds; a green suite after the
change would not have, which is why they assert the *negative*.

The general lesson: for a loop, an invariant is not a predicate to *check at the edges*,
it is a predicate to *assume over the whole state space it describes*. Asserting it at the
back edge is necessary and not sufficient; the header has to forget what it cannot know.

## A call to `core` made the whole path unknown, and modelling it needed a tag that is a term

The MIR frontend's biggest coverage gap was not a parser shape or a width wall: it was that
any call into `core` was unmodelled, so `a.checked_add(b)` — the idiomatic way to write
arithmetic that must not panic — made every obligation downstream of it `incomplete`. The
corpus scoreboard said so in one line, `is_nonzero_after  incomplete  call to unmodelled
function ...checked_add`, and that line is why the scoreboard exists.

The fix is `src/mir/intrinsics.rs`: `checked_*`, `saturating_*` and `wrapping_*` are computed
from their operands rather than refused. Three things about it are worth carrying forward.

**The refusals are the design, not a limitation.** Only `checked_div`/`checked_rem` may model
division. `saturating_div` and `wrapping_div` *panic* on a zero divisor, and modelling a
panicking operation as total would hide a panic — the one thing this frontend must never do.
The shifts are refused because the families genuinely disagree: `wrapping_shl` reduces the
amount modulo the width, the engine's variable shift saturates to zero, and `checked_shl`
returns `None` past the width. Three behaviours under one name is not something to guess at,
and a wrong guess is not a weaker proof, it is a false one. So refusal happens at two layers
and a test pins both: a name whose operator is unknown does not `classify` at all, while a
name that classifies (`saturating_div`) is refused by `is_modelled`/`eval`. The first draft of
that test asserted `saturating_div` does not classify, and the failure was the useful kind — it
showed the two layers were real and the test was naming the wrong one.

**A `checked_*` result is an `Option`, and its tag is a *term*.** This is the part that made
the plumbing non-trivial. `checked_add` on a `u8` is `Option<u8>`: rustc lowers the consuming
`match` to a `switchInt` on `discriminant(_2)`, and reads the payload through a
`Proj::Downcast(Some)` place. A tag modelled as a constant would take one arm always. It has
to be `ite(fails, 0, 1)`, where `fails` is the same overflow predicate the `assert` reads, so
the `switchInt` goes the right way on each path. The payload is recorded *unconditionally*
under the `Some` projection, and that is sound precisely because rustc emits the downcast read
only inside the arm where the tag is `1` — the path condition is the gate, so no extra gate is
needed. The width is the *operand* width, not the destination's: sizing the payload from the
`Option<u8>` local would ask the engine for a 64-bit overflow test.

Three smaller traps fell out of the same work, each a place where a plausible reading is wrong:

* `Rvalue::Discriminant` was sizing the tag from the dump's `isize` rather than from the
  payload width, and returning `Unknown` when no tag was recorded instead of `Val::Unknown`
  for an unknown *tag*. A modelled `Option` local has no `locals` entry — its value *is* its
  tag — so `Env::get` needed a fallback to the `discriminants` map, or `discriminant(_2)` and
  `move _2` both came back unknown.
* The downcast payload read `((_2 as Some).0)` is *one* step, not two: the projection loop
  consumed the `Downcast` and then processed the trailing `Field(0)`, which looked the payload
  up in the tuple map and overwrote a good value with `Unknown`. The loop now consumes both.
* `parse_rvalue` matched the ` as ` cast form before trying a `copy`/`move` of a place, so a
  downcast place did not parse. Checking the place form first fixes it — the same shape of
  ordering bug as the earlier `const ... as ...` case, in the opposite direction.

**The oracle is Rust itself, enumerated.** The model claims to implement `core`'s definition,
so the unit tests in `src/mir/intrinsics.rs` compare against the real `u8::checked_add` and
its family over *all* of `u8` and all of `i8` — 65536 pairs per case, cheap because the term is
built once and walked per pair rather than reset per pair. That is what pins the signed rules,
which no unsigned test can see: `-1 + 1` does not overflow, but the unsigned carry test fires
on it, so an unsigned-only model would report a panic that is not there. `i8::MIN / -1` and the
width limits are checked the same way. The terms are read back with `smt::evaluate`, which is
the concrete semantics of the symbolic language, so the test compares *values* and not just
`Some`/`None`.

The scoreboard moved from 4 of 14 decided to 10 of 14, and the remaining four each name
themselves in the `detail` column — an unreadable `requires` (`c.lo <= c.hi`, `xs.len() > 0`)
and a tuple-returning `ensures` (`ret.0 <= a`). Those are the next gaps, and they are parser
gaps rather than engine ones, which the scoreboard says without being asked.

## An inlined call must restore the caller's loop cut, or the caller unwinds a loop it had cut

Cutting a loop at its invariant is a property of a *function*: the `Cut` names the header and
back edges of one loop in one function's CFG. Entering an inlined callee therefore clears
`cut`, correctly — the caller's invariant says nothing about the callee's locals. The return
path then copied the callee's `cut` into the resumed caller, which is the bug: a callee that
returns from a function with no loop leaves `cut` as `None`, so the caller resumed *inside its
own loop* with no cut. The next edge into the header was unwound rather than checked against
the invariant, and once the loop passed `DEFAULT_UNWIND` the function was reported
`Incomplete` — a valid proof discarded, not a false one, but a defect all the same.

The frame already had the fix's shape: `saved_env` is set aside at call entry and restored on
return, for the same reason. `saved_cut` follows it exactly. Restoring the cut is the whole
change; the callee's own cut is dropped because the callee has returned.

What made this reachable *now* is the exact-name lookup. Before it, a user function named
`wrapping_add` was answered by `intrinsics` as `a + b`, a leaf that never entered a frame, so
the caller's cut was never disturbed. Sending such a function through the inliner — the right
fix for the false proof it caused — exposed the return path's missing restore. A change that
fixes one defect can activate another that was latent behind it.

The teeth are two tests, and the second matters as much as the first:
`an_invariant_survives_an_inlined_call_on_the_loop_edge` requires the loop to verify across
the call (it fails on the pre-fix code), and `an_inlined_call_does_not_rescue_a_weak_invariant`
requires the same loop with `ensures: ret == 0` to still be refuted. Restoring the cut must
restore the proof the invariant actually carries, not resurrect one that was never there.


## The `rustc_public` oracle: what the text parser is checked against, and why it is a separate crate

The MIR frontend reads the **textual** `--emit=mir` dump. That is the crate's stated gap 2:
a rustc release that reprints the dump can break the parser, and the parser is the only thing
that reads the dump, so nothing else notices. `tools/mir-oracle` closes that loop by asking
`rustc_public` — the compiler's own public API — for the same programs' **typed** MIR and
comparing a per-function *shape*: block count plus the panic guards `rustc` inserted, in block
order. Structural, not textual, because the two dumps are not byte-identical (the typed one
omits `copy` qualifiers, prints `let  _4` with different spacing, and nests `scope` blocks),
so a text diff fails on cosmetics and proves nothing.

Traps that cost time, in the order they cost it:

* **`rustc_private` needs four `extern crate`s, not one.** `extern crate rustc_public;` alone
  fails to link; `rustc_driver`, `rustc_interface` and `rustc_middle` must be declared too,
  because the `run!` macro expands to code naming all three. The error is `cannot find module
  or crate rustc_middle in this scope` pointing at the macro invocation, which reads as a
  missing dependency rather than a missing `extern crate`.
* **`run!` wants `&args`, and argv[0] is the program name.** `run!(&args, …)`, not
  `run!(args, …)`. Passing a `Vec<String>` is a type error against `&[String]`; passing a
  slice with the file first (no program name) makes rustc read the file as the program name.
* **`--out-dir` is mandatory.** `rustc_public` runs a real rustc; without `--out-dir` it drops
  `lib<stem>.rlib` next to the source file, so every oracle run litters the repository. The
  oracle points it at a temp directory. This is easy to miss because the run still *succeeds*.
* **The binary needs the sysroot on its runtime path.** A `rustc_private` binary links
  `librustc_driver-*.so` but cargo does not add the sysroot to its rpath, so it builds and then
  dies with `cannot open shared object file`. `build.rs` bakes `-Wl,-rpath,$(rustc --print
  sysroot)/lib` in, using the `RUSTC` cargo is building with. `run.sh` sets both `RUSTC` (what
  cargo builds *with*) and `DISCHARGE_RUSTC` (what the frontend *runs*) to the same nightly.
* **`rustc-dev` alone is not enough: `llvm-tools-preview` is required too, and the error
  misreports the cause.** `rustc` links `libLLVM`, and cargo puts
  `<sysroot>/lib/rustlib/<target>/lib` on the build script's `LD_LIBRARY_PATH`. A bare
  toolchain keeps `libLLVM` in `<sysroot>/lib`; it reaches `rustlib/<target>/lib` only via
  `llvm-tools-preview`. That directory *takes precedence* over the `$ORIGIN/../lib` RUNPATH in
  the `rustc` binary, so with only `rustc-dev` the `build.rs` cannot even start
  `rustc --print sysroot` — and the visible symptom is the *linker* failing with `unable to
  find library -lLLVM-...`, two steps later. A `-L <sysroot>/lib` flag cannot fix it (the
  failure is `rustc` failing to start, not `ld`), so `build.rs` now panics naming the
  component instead of returning quietly. Install
  `rustup component add rustc-dev llvm-tools-preview --toolchain nightly`.
* **`cargo clippy` ignores `RUSTC` when choosing its driver.** `RUSTC=<nightly> cargo clippy`
  still runs the *default* toolchain's `clippy-driver`, so it checks a `rustc_private` crate
  with the stable driver and reports `can't find crate for rustc_driver` — which reads like a
  missing component and is not. Use `cargo +nightly clippy`, and install `clippy` onto the
  nightly (a `--profile minimal` toolchain does not ship it). `cargo build` and `cargo test`
  *do* honor `RUSTC`, so only the lint step needs this.
* **`cargo install` is not idempotent, which makes a warm cache a trap.** The Kani job cached
  `~/.cargo/bin/cargo-kani` and then ran `cargo install` unconditionally; `cargo install`
  refuses to overwrite (`binary cargo-kani already exists in destination`), so the job could
  only pass on a cold cache. Guard the install on the binary being absent, and version the
  cache key so a cache left in the broken state is dropped.
* **The crate is `exclude`d from the workspace, not a member.** A member would make
  `cargo build --workspace` require a nightly, which breaks the stable zero-dependency build
  that is the whole point of the crate. `exclude = ["tools/mir-oracle"]` plus `cargo build`
  from inside `tools/mir-oracle`. `cargo metadata` lists exactly `discharge` and
  `discharge-arithmetic`, so gate 4 still sees a two-line tree.
* **`rustc_public::mir::body` is private but glob-re-exported.** Import from
  `rustc_public::mir::{…}`, not `rustc_public::mir::body::{…}`. `Local` is `pub type Local =
  usize`, not a tuple struct, so `Local(0)` does not compile — use `Place::from(0usize)`.

The oracle has teeth and it was checked: flipping one arm of `PanicKind::from_text_message`
(Add -> Mul) makes the run exit 1 with 7 actuator functions and 4 realistic functions named
and their two panic lists printed. A tool that can only say "agree" is not evidence.

### Two things the first version of the shape could not see

Both were gaps in the *checker*, which is the worst place for one, and both are the same
mistake: reducing a function to a summary that is not injective, then comparing summaries.

* **The shape recorded a guard's kind but not its polarity.** `assert(!move _3, "…overflow")`
  and `assert(move _3, "…overflow")` shaped identically, though they describe opposite
  programs. A printer change that flipped a leading `!` therefore passed. The parser had
  always carried `negated`; the shape — the thing compared — did not. `FnShape.panics` is now
  `Vec<AssertShape>` with `AssertShape { kind, polarity }`. On the typed side the source is the
  `Assert` terminator's `expected` flag, which is the value for which control *continues*, so
  it is the **inverse** of the text side's `!` — `polarity_of` is a one-line function and
  getting it backwards makes 21 actuator and 6 realistic functions disagree, which is how it
  was checked. A useful side effect: the real asymmetry shows up, that `Bounds` is `True` while
  every arithmetic guard is `Negated`.
* **The gate's cost was the test profile, not the algorithm.** `prove::ENUM_BUDGET`
  is documented as "about two seconds of tight loop", but that figure is a *release*
  calibration. Cargo's default test profile is unoptimised, and the enumerations are
  tight integer loops, so the same `2^32` walk cost ~21 s in the gate against ~2.6 s
  optimised — and three sibling tests did it. The fix is `[profile.test] opt-level = 2`
  in the workspace root, which took `scripts/test-count.sh` from 1m50s to 15.5 s
  without touching a single proof. Two things to keep in mind: `[profile.test]` only
  takes effect in the workspace root manifest (a profile in a member is ignored, and
  cargo does not warn), and it applies to the *library* the integration tests link,
  which is where the hot loop actually lives. Do not buy the speed with
  `debug-assertions = false` — this is an arithmetic crate, and the `checked_*` tests
  are where a silent wrap would hide; `the_test_profile_is_optimised_without_losing_its_checks`
  fails if someone tries.
* **A budget in cases is not a budget in seconds.** `ENUM_BUDGET` bounds the *count*
  of cases, not the wall-clock cost. An obligation that does more work per case, or a
  build without optimisation, is slower for the same count. Calibrating a case budget
  in release and enforcing it in debug is exactly how a "2 second" bound became a
  20 second gate.
* **A coverage check that compared first counterexamples.** `fixed_add_no_overflow`
  skips the points its precondition rejects, which is only sound if the rectangle it
  walks is *exactly* the precondition's set. The first version of the check ran both
  walks on one goal and compared their verdicts — but a walk stops at its **first**
  counterexample, and two different rectangles can share one. At width 8, bounds 200
  and 199 both fail first at `(1, 198)`, so the check passed while the 199 rectangle
  omitted every pair containing 200 that the precondition admits. Coverage is a
  property of the *domains*, so it has to be checked on the domains, with no goal in
  sight. The replacement compares the two bounds directly and is O(1): for a square
  precondition (`a <= k && b <= k`) the two sets are equal exactly when the bounds
  are equal, since neither can be a proper subset of the other. The general lesson is
  the same one the shape gaps taught: a check whose verdict depends on the thing it
  is checking is not a check. A brute-force sweep of the domain was written first,
  agreed with the O(1) version everywhere, and was thrown away — it cost 11 s and
  added no evidence.
* **Bare names were treated as unique keys.** `impl A { fn check }` and `impl B { fn check }`
  in one file both reduce to `check`, and both sides used a single-slot map, so the first was
  silently replaced by the second. Dropping it from the text parser produced *zero*
  differences. Both sides now keep a `Vec<FnShape>` per name and compare it sorted, as a
  multiset: the enumeration order differs between the two sources and is not worth asserting,
  but the set of shapes under a name is exactly what a lost method changes.

Exit codes are four-way on purpose: `0` agree, `1` a shape disagreed, `2` the oracle could
not run (no nightly, or a missing `rustc-dev` / `llvm-tools-preview` component), `3` the
oracle could not be *built* though the components are present. Gate 9 skips only on `2` and
fails on everything else, so "the toolchain is missing" is never reported as a parser failure
nor as a pass — and, the mirror-image bug, a compile error in the oracle is never reported as
a missing toolchain and quietly skipped. `run.sh` decides between 2 and 3 by probing for
`librustc_driver-*.so` and `libLLVM-*` in `$sysroot/lib/rustlib/$host/lib` directly, rather
than by asking `rustup component list` (which answers for a toolchain *named* `nightly`, and
`DISCHARGE_RUSTC` may point elsewhere).

## A projection is a binding decision, not a grammar rule

Contracts could name arguments and `ret`, and nothing else. `requires: b.lo <= b.hi` on a
`&Bounds` argument was `skipped` with "unknown name", because the expression language had no
dot operator and no notion of a field. Two of the fourteen functions in
`examples/mir_targets/realistic.rs` were lost to that — `pick_from` and `clamp_by_value` — and
a tuple return (`split`, `ensures: ret.0 <= a`) was lost to the same gap one level down.

The first idea was to add a projection operator to the parser. That is the wrong shape: it
puts the same decision (which field is this, how wide is it) at every operator that can
appear next to a place. Instead each readable field is *rewritten* to a mangled identifier
(`c.lo` → `c__f0`) before parsing, and bound to a variable of the field's own width and
signedness. The grammar stays "arithmetic over names"; the projection is one binding decision,
made in one place.

What makes this work, and the parts that would have been silent bugs:

* **The layout is not in the MIR.** The dump prints `_1: &Bounds` and never the fields, so
  both the field *index* (declaration order) and the *width* have to come from the source.
  That is consistent with how contracts are already read (doc comments, since attributes need
  a proc-macro and a proc-macro is a dependency), and it means a contract and the layout it
  names come from the same bytes. A struct the layout reader does not find yields no bindings,
  and a contract naming one of its fields is refused — not checked against a guessed width.
* **Two fields must not alias, and a hash is how they would.** The first version derived the
  field's variable slot from an FNV-1a hash of `arg.field`. A collision there is not a missing
  proof but a *wrong* one: `c.lo <= c.hi` becomes `x <= x` and verifies vacuously. A sequential
  counter cannot collide, so there is nothing left to argue about. The tripwire is
  `field_alias_tripwire` in `realistic.rs` — same shape as `clamp_bounds` but claiming
  `ret >= c.hi`, which is false whenever `v < c.lo <= c.hi`. It must FAIL, and its
  counterexample names two distinct variable indices; `tests/mir.rs` requires both the failure
  and the two distinct names.
* **The contract's field and the body's field must be the same variable.** The contract binds
  `c.lo` to a variable; the body reads `((*_1).0)`. If those were two fresh variables the proof
  would be vacuous in the direction that matters. `FieldEnv.seeds` carries `(local, field,
  var)` to the executor, which seeds its `fields` map with exactly those variables, so the two
  are made to agree by construction rather than by convention.
* **A deref is transparent only as a whole place.** `*_1` for a `&T` argument names the same
  value `_1` does, because `Ty::Ref` is modelled as its referent. The gate has to be `i == 0`
  as well as "the local is a reference": `*(_1.0)`, a field that is itself a reference, is a
  *different* pointee and `deref_ok` says nothing about it. Reading the field as though it were
  the argument's referent is a wrong value, not a missing one.
* **A projection that cannot be resolved is refused, never dropped.** `c.lo` where `lo` is not
  a field is an error naming the field (not the parser's "expected a comparison operator",
  which is what the `.` produced before the diagnostic was added), and `ret.0` on a
  non-aggregate return is refused. A dropped conjunct would verify the function against a
  weaker contract than the source states — the same class of bug as a skipped function
  reporting `ok`.
* **`ret` for an aggregate is `None`, not a fabricated word.** A tuple return has no single
  word, so `post` receives `Option<Var>` and the parser refuses a bare `ret` while still
  resolving `ret.0`. Passing a fresh unconstrained word would have let `ensures: ret == k`
  pass on a tuple return by luck.

Coverage on `realistic.rs` went from 10 of 14 decided to 13 of 14 when field and tuple support
landed. `clamp_bounds` was added to `actuator.rs`, the regression corpus where *every* function
must be decided, so a regression in field support is a failing test rather than a quietly lower
number. The `rustc_public` oracle (gate 9) agrees on 31 actuator and 15 realistic functions with
the new shapes.

## A slice length is an input, and its elements are indexed by value

The last `realistic.rs` skip was `first_of(xs: &[u8]) -> u8 { xs[0] }` with
`requires: xs.len() > 0` / `ensures: ret == xs[0]`. It is the same class of gap as a field —
a contract naming something the expression language had no way to name — but the *shape* of
the fix is different, and the difference is the interesting part.

A slice has no length in its type. `&[u8]` is the whole type; the length is whatever the caller
passed, so `xs.len()` cannot be a constant the frontend computes. It is a *symbolic input*, on
the same footing as an argument. The body agrees: rustc lowers `xs[0]` to `_3 =
PtrMetadata(copy _1)` (the length), `assert(Lt(_2, _3))` (the bounds check), then `(*_1)[_2]`.
The contract's `xs.len()` and the body's `PtrMetadata(_1)` have to be one variable or the
bounds check cannot be discharged from the precondition, so the length is bound once in
`FieldEnv` and handed to the executor as a `len_seed` — the slice analogue of the field seeds.

The parts that would have been silent bugs:

* **Elements are indexed by value, not one variable per slice.** The tempting model gives a
  slice a single "element" variable. Then `xs[0] == xs[1]`, and `slice_alias_tripwire`
  (`ensures: ret == xs[1]` on a body returning `xs[0]`) would verify. Elements are keyed by
  `(local, index)` instead, so two indices are two inputs. The tripwire must FAIL, and its
  counterexample assigns the two elements different values; `tests/mir.rs` requires both.
* **A symbolic subscript is refused on a slice, and modelled on an array.** `xs[i]` with `i` a
  parameter has no single element to name on a slice, and reading "some element" would make
  `xs[i]` a different value per read — a wrong proof, not a missing one. An *array* is
  different: its length is in its type, so `a[i]` is the exact ite chain over `0..N` and is
  modelled (see the symbolic-index section below). The distinction is the domain being finite,
  not the subscript being symbolic.
* **The element width is the referent's, not the length's.** `&[u8]` has `u8` elements and a
  `usize` length. Taking the element width from the length variable sizes every read at 64 bits
  and mis-models the bounds check.
* **The element is created on first read, which `get` cannot do.** `Env::get` takes `&self`, and
  the first read of `xs[0]` has no variable yet. A `read_slice_index(&mut self, …)` on the
  operand path creates it; the second read of the same index finds the same variable. Binding
  the *contract's* element references up front (`bind_slice_refs`) keeps the postcondition
  closure — which cannot hold a `&mut` — evaluating against the same bindings.

Coverage on `realistic.rs` is now complete: every function is decided, and the three
tripwires (`field_`, `slice_`, `array_alias_tripwire`) are decided *and must fail*, which is
what makes them evidence rather than decoration. `first_of` was added to `tests/mir.rs` as a
must-verify case, so a regression in slice support fails a test.

### An array's length is a constant, not an input

`[u8; 4]` and `&[u8]` look alike at the use site and are not alike at all. A slice's length is
whatever the caller passed, so it is a fresh input. An array's length is *in the type*: `4` is
the only length the value can have. Binding it to a fresh variable would be the unsound
direction — the contract would be proved for some length the caller chose, when there was
nothing to choose, and a contract proved at length 4 would appear to hold at any length. So
`bind_array_len` binds `a.len()` to the constant word `4`, and the body's bounds check
(`assert(Lt(_2, const 4_usize))`) is discharged from the index being a literal below 4.

The rest of the machinery is shared with slices, deliberately: `FieldEnv::indexed` maps a name
to `(local, elem_w, Option<fixed_len>)`, where the length is `Some(n)` for an array and `None`
for a slice. One map, one element model, one scanner (`bind_index_refs`) — an array is not a
second feature bolted on, it is the same feature with the length known. `bind_indexed_elem`
refuses an index `>= n` for an array rather than binding a fresh variable, because the element
does not exist and a fresh variable there would make a meaningless contract look meaningful.

### A literal's width comes from the operand, not from the scope

This is the bug array support exposed, and it is worth recording because the symptom pointed
nowhere near the cause. `arr_pre(a: [u8; 4]) -> u8` with `ensures: ret <= 255` came back
`incomplete`. The body was trivially fine. The cause: a contract literal was built at the width
of the *widest name in scope*, and an array or slice length is a `usize`. So `255` was a 64-bit
constant compared against an 8-bit `ret`. `smt::cmp` refuses mismatched widths by setting the
engine's `ill_formed` flag, and **an ill-formed term makes every obligation in the run
`Unknown`** — so the function was undecided for a reason that had nothing to do with it. The
same bug had been silently present for slices: `slice_le` was `incomplete` at HEAD.

The fix is a per-use width decision, in three parts, and each part is a separate way to be
wrong:

* **Build the literal wide enough to hold its own value.** Sizing it at the scope's width
  instead masks it: `a <= 300` for a `u8` becomes `a <= 44`, which is a weaker claim that could
  pass. So the constant keeps its exact value and the width is chosen later.
* **Resize the constant to the other operand's width (`align_widths`).** Zero-extend for an
  unsigned operand, sign-extend for a signed one. A value that does not fit is *refused*, not
  truncated: `a <= 300` for a `u8` is an error naming the value and the width, because the
  alternative is a proof of the wrong proposition.
* **Narrow by truncation, not by rebuilding from the value.** A negative literal is the bit
  pattern `2^w - 10` at its source width. Rebuilding `word(val, wide)` from that value hands
  `wide` a number that does not fit and sets `ill_formed` again — the very flag being avoided.
  Taking the low `wide` bits is the same bit pattern, and the `fits` check is what keeps it
  from being silent.

`i8::MIN` and friends are the same lesson from the other side: the bound must carry the width of
the type it *names*. `i8::MIN` is `0x80`, exactly 8 bits. Building it at a wide scope width and
narrowing back tested a 64-bit `128` against the signed 8-bit range and refused a bound that is
in range by construction.

Each of these has a test in `tests/mir.rs` written against the *evaluator*, so it does not
depend on a corpus function happening to be skipped for an unrelated reason. Two of them failed
when first written and found the masking and truncation bugs above.

The rule is not a comparison rule, it is a *meet* rule, and it applies wherever two operands meet:
`parse_expr` and `parse_term` call the same `align_widths`. `ret == a + 5` with a slice length in
scope had the identical failure — an 8-bit `a` added to a 64-bit `5` — and was `incomplete` for
the same reason. That the first fix was written only in `parse_cmp` is what made the arithmetic
case a separate bug rather than the same one.

### A symbolic subscript is modelled on an array and refused on a slice

`a[i]` and `xs[i]` are the same source shape and are not the same problem. The difference is
not that one is symbolic and one is not — both are — but that one has a *finite domain*. An
array's length is in its type, so `a[i]` ranges over a set the frontend can enumerate:
`ite(i == 0, a0, ite(i == 1, a1, … ite(i == N-1, a_{N-1}, 0)))`. That is not an approximation of
`a[i]`, it is a *definition* of it. A slice's length is a symbolic input, so there is no domain
to enumerate and `xs[i]` stays the refusal it always was. The feature is drawn at the domain,
and `MAX_INDEX_CHAIN` bounds it so a large array is refused rather than turned into a term the
solver cannot hold.

Three things had to be true for the chain to be sound, and each is a separate trap:

* **The chain is only `a[i]` where `i < N`, so the precondition must establish that.** The chain
  has to return *something* for `i >= N` (it falls through to the last element). Checking a
  contract there would check it against a value that is not `a[i]`. So `index_guards` reports
  `(index var, N)` for every symbolic subscript, and `verify_function` *proves* `pre ⇒ i < N`.
  If it does not hold, the function is `Skipped` with a reason naming the bound. The tempting
  alternative — conjoin `i < N` into the precondition — is unsound in the direction that
  matters: it strengthens what the source asked to be verified, so a contract proved under
  `i < 4` would be claimed to hold without it.
* **The chain must be built from the *same* element variables the body reads.** The parser
  rewrites `a[i]` to the chain, and the chain is built from `elem_seeds` — the very variables
  the executor is seeded with. If the contract's `a[i]` were built from fresh variables, the
  postcondition would be about one array and the body about another, and every proof would be
  vacuous in the direction that matters. `bind_sym_index` therefore binds *every* element of
  the array up front, not on demand: an element the contract did not bind would be created
  fresh by the body's first read.
* **Only the index that was bound has a chain.** `a[j]` where only `a[i]` was bound must not be
  rewritten to the `a[i]` chain — that would prove `a[j] == a[i]`, false for every `i != j`. The
  rewrite checks `sym_index_name` for the exact index argument before replacing, so a name that
  merely looks like the bound one is left for the parser to refuse.

The index is a *name the contract may use* — an argument — and it is bound to that argument's
own variable, so `requires: i < 4` and the chain's guard are the same `i`. A compound index
(`a[i + 1]`) has no name to bind and is refused rather than mis-modelled.

`tests/mir.rs` pins all four sides: the chain verifies, an unbounded index is refused, a
different index is refused, a slice subscript is still refused, and a *false* postcondition
about `a[i]` fails with a counterexample (so "verified" cannot be the chain being a constant
the postcondition happened to accept). The corpus entries are
`array_symbolic_index`, `array_unbounded_index_refused`, `array_wrong_index_refused` and
`slice_symbolic_index_refused`.

### A write has to land where the read looks

The three soundness holes below were all the same shape: the environment held a
value for a place in *two* places, and a write updated one of them. Each produced
a *false proof* — a contract that does not hold, reported `verified` — which is
worse than a refusal, because it is the answer that gets trusted. They were found
by a review that read `Env::set` and `index_elem` side by side, not by a test; the
tests that now pin them were written after.

* **An element write went to the wrong store.** `Env` kept slice and array
  *arguments*' elements in `indexed[local].elems` (seeded from `elem_seeds`, and
  what the ite chain is built from) but stored a write with `elems.insert((local,
  index), v)` — the map for array *literals*. The read consulted the first, the
  write updated the second, so `a[0] = 0; a[i]` read the pre-write `a[0]` and
  `ensures: ret == a[i]` under `i == 0` was *proved*. `set` now routes an element
  write through `write_elem`, which picks the same store the read picks, and the
  `(*_1)[0] = v` and `_1[_2] = v` forms are handled too. The general rule: the
  write path and the read path must key on the same distinction, and when there
  are two stores the code that writes has to know which one the reader will use.

* **A write the store cannot represent has to poison, not be dropped.** An element
  write of an aggregate, or through a *symbolic* index (`_1[_2] = v`), has no
  per-index slot: the first has no word to store and the second would have to
  update every element the chain could select. Dropping it leaves the seeded value
  readable — the same stale read, one level down. `Indexed::poisoned` marks every
  element unknown instead, keeping the *length* (a write does not change a type's
  length). `index_elem`, `read_indexed` and both `get` arms check it. An unknown
  element fails a postcondition as an unreadable contract; it does not silently
  become the old value.

* **A whole-place assignment left the parts behind.** `c = d` wrote `locals[c]`
  and left `fields[(c, 0)]` holding the *argument's* field, so `c = d; c.lo` read
  the stale `c.lo` and `ensures: ret == c.lo` was proved against the wrong struct.
  `set` now calls `forget_parts` on a whole-place write, dropping the field,
  element, payload and tag maps for that local (and poisoning its elements).
  `Val::Agg` is the deliberate exception: an aggregate rvalue (`_0 = (a, b)`, the
  `(result, overflowed)` of a `checked_*`) writes its own parts inside
  `eval_rvalue` and then returns `Val::Agg`, so clearing there would delete the
  parts that were just written and turn a modelled tuple back into an unknown one.
  Clearing the derived state on a whole-value write is the conservative direction;
  the exception is the one case where the derived state *is* the value.

* **A generated name must not be able to shadow a real one.** Bindings are named
  by mangling (`a__len`, `c__f0`, `a__chain`) and handed to the parser *after* the
  arguments, so an argument that happens to be called `a__chain` would be shadowed
  by the chain and a contract naming it would be checked against the array. The
  fix is not a less guessable separator — any scheme is guessable — but to record
  every source name in `FieldEnv::declared` and refuse a generated name that
  collides (`name_is_free`), so the binding is dropped rather than allowed to
  shadow. The collision is a refusal, which is the honest answer: the source
  chose a name the mangling wanted.

The remaining gap this exposed is separate and stays open: a `&mut [u8]` *slice*
argument lowers a write through `&raw const (fake) (*_1)`, whose `PtrMetadata` the
frontend does not model, so the function is `incomplete` before any write is
reached. A `&mut [u8; 4]` does not — it goes through a plain reborrow — and is
modelled. That is why the corpus tripwire for the reborrowed form is
`mut_ref_array_write_then_symbolic_read`, not the slice.

`tests/mir.rs` pins each hole by name: `an_element_write_reaches_the_symbolic_chain`
(requires `Failed`, so a counterexample is the evidence the chain saw the write),
`an_element_write_through_a_mutable_reference_reaches_the_chain`,
`a_whole_struct_assignment_invalidates_its_fields` (requires *not* `Verified` — the
write poisons the field, so the postcondition is unreadable),
`a_generated_binding_cannot_shadow_an_argument` and
`a_generated_length_binding_cannot_shadow_an_argument`, plus
`a_write_cannot_prove_a_stale_contract` over the corpus entries
`array_write_then_symbolic_read`, `mut_ref_array_write_then_symbolic_read`,
`generated_name_shadows_argument` and `struct_reassign_then_field_read`.

## A call boundary is a real boundary: what crosses it and what must not

Four soundness holes and two completeness holes lived at the same place — the
inlined call — and in the same shape of mistake: a value or a type was carried
across the boundary when it should have died with the frame, or dropped when it
should have crossed.

**A by-value aggregate is the callee's copy; a reference is the caller's storage.**
The frontend models `&T` as its referent (the single-owner reading, not an aliasing
model), so a `&mut [T; N]` argument and the caller's local denote the same store:
the callee's post-state *is* the caller's post-state and is copied back on return
(`Frame::by_ref_indexed`). A by-value `[T; N]` is the opposite: the callee got its
own copy, its writes must die with the frame, and nothing is copied back
(`Frame::by_value_indexed` records the pair only so the return-merge can tell the
two apart). Sharing the copy — the tempting way to make a callee's element read
agree with the caller's — makes `let b = f(a)` mutate `a`, so a caller contract
about `a` is checked against a value that never existed. The corpus tripwires are
`caller_of_written_copy` (by-value write must **not** leak; `ret == 0` is false, so
it must fail) against `caller_of_clear_head` (a `&mut` write **must** be visible).

**A constant operand carries its own signedness.** `0 < a` lowers to
`Lt(const 0_i8, copy _1)` — the constant is the *left* operand, and `Const::UInt`'s
type suffix is the only place the signedness appears. Reading a constant as
unsigned made `0 < a` unsigned, under which `i8::MIN` (`0x80`) is the *largest*
value, so `requires: a == i8::MIN; ensures: ret == 1` on `if 0 < a { 1 } else { 0 }`
was **proved** — a reachable false proof, since `i8::MIN` is negative and the
branch is never taken. The fix is `operand_signedness`, which returns `Option<bool>`
and *refuses* (`None`) when the type cannot be resolved rather than defaulting to
unsigned; every caller (`eval_binary`, the checked intrinsics, `try_intrinsic`)
propagates the refusal as `Val::Unknown`. A wrong signedness is not a missed proof
but a wrong branch, which is a wrong answer. The unit test
`a_constants_signedness_comes_from_its_suffix` pins all three answers, because the
bug was a *default* and a test that only checked the signed case would pass the
moment the default came back.

**A tuple component and a struct field are two spellings of "component N".**
`_3 = (a, b)` stores the components under an *index* projection (`elems`), but rustc
prints the read back as `_3.0` — a *field* projection (`fields`). The two have to
meet in one store (`Env::get`'s `Proj::Field` arm falls back to `elems`), or
`let t = (a, b); t.0` reads `Unknown`. A local is a struct or a tuple and never
both, so the fallback can only hit for the tuple case; a struct field that is
genuinely unwritten finds nothing in either store and stays `Unknown`.

**A tuple return's components cross the call boundary with the aggregate.** The
callee stores its result in its *own* return place (`_0.0`, `_0.1`); the caller's
`min2(a, b).0` reads `_2.0`. Carrying only the aggregate loses the components and a
contract about them is unreadable rather than checked. They are copied under the
*destination's* local, and only the ones the callee wrote — a path that left `_0.1`
unwritten leaves the caller's `dest.1` unknown rather than inventing a value. The
tripwires `tuple_component_tripwire` and `min_call_tripwire` claim the *wrong*
component and must fail.

**A tuple-return postcondition is checked on the components a contract names.**
`ret.0` of a `(bool, u8)` is a `bool` in the type but a one-bit word in the
postcondition, so the component is widened on read-out (`Val::Bool` →
`ite(p, 1, 0)`) — without it the name is unbound and the contract is refused. And
the up-front parse probe (`verify::verify_fn`) binds only the components the
contract *names* (`spec::named_ret_components`): binding every declared component
made a `(u8, &u8)` return unprobeable (component 1 is a reference with no bit
width), so a contract about `ret.0` alone skipped the whole function. A component
the contract names and that has no width is still refused — then the name really
cannot be resolved.

`tests/mir.rs` pins each by name:
`a_helper_that_indexes_its_parameter_reaches_the_caller_element`,
`a_write_through_a_reference_reaches_the_caller`,
`a_by_value_helper_cannot_write_the_callers_array`,
`a_constant_left_signed_compare_is_signed_not_unsigned`,
`a_postcondition_can_name_a_bool_tuple_component`,
`a_reference_component_the_contract_does_not_name_does_not_skip_the_function`,
`a_tuple_locals_component_can_be_read_back`,
`a_tuple_returning_calls_component_reaches_the_caller` and
`a_tuple_component_read_cannot_prove_the_wrong_component`, over the corpus entries
`head`/`caller_of_head`, `clear_head`/`caller_of_clear_head`,
`caller_of_written_copy`/`clear_copy`, `signed_const_left_false`/`_true`,
`bool_component`, `first_component_only`, `tuple_local_component`, `min2`/`min_call`
and the two tuple tripwires.

## A widening cast needs the *source's* signedness, and `truncate` is not it

`Rvalue::Cast` used `smt::truncate` for every target width. `truncate` zero-fills,
so `-1i8 as i16` was modelled as the bit pattern `255` — and
`requires: a == -1; ensures: ret == 255` on `a as i16` was **proved**, a second
reachable false proof of the same family as the constant-left comparison: a value
operation that silently lost its sign.

The two widening directions need *opposite* rules, so no single rule is right:
`i8 as i16` sign-extends (`-1` stays `-1`), `u8 as u16` zero-fills (`255` stays
`255`). The source operand's signedness decides, via the same `operand_signedness`
the comparison and shift paths use — `Some(true)` → `smt::sign_extend`,
`Some(false)` → `smt::truncate`, and `None` (the source type could not be read) →
refuse, because zero-filling a signed value is the false proof above and
sign-extending an unsigned one turns `255u8 as u16` into `65535`. `sign_extend`
truncates first when the target is no wider, so a *narrowing* cast (`300i16 as u8`
→ `44`) is unaffected and `truncate`'s behaviour is unchanged for it.

`tests/mir.rs::a_widening_cast_respects_the_sources_signedness` pins all four
directions — the two true contracts must verify and the two false ones must fail —
over `widen_signed_true`/`_false` and `widen_unsigned_true`/`_false`, because a
test that only checked the signed case would pass again the moment the rule went
back to a single default.

## Next stage: the signedness work is a *rule*, so let the engine state it

Both false proofs fixed in this round were the same bug wearing different
clothes. A value operation silently dropped the signedness of its operand:
`0 < a` compared `const 0_i8` as unsigned, and `a as i16` zero-filled a signed
source. The repair went in at each *call site* of `operand_signedness`. That is
the shape of fix that leaves a third case behind, so the next stage is to make
the rule structural rather than per-site.

**Stage 1 — make the width-and-signedness rule a type, not a habit.** DONE.
`Val::Sym` is now `Val::Sym(Var, Sign)`, and `Sign` has *three* cases:
`Signed`, `Unsigned`, and `Unknown` for a value whose dump printed no type. The
third case is the whole point. With only two cases, a site that could not read
the sign had somewhere to fall back to, and both false proofs were exactly that
fallback: a suffix-less `const 0_i8` read as unsigned, and a cast source whose
sign was dropped. With three cases, every signedness-sensitive site has to say
what it does when the sign is missing, and the compiler names the ones that do
not -- which is how the four sites below were found rather than remembered:

* `eval_binary` -- a relational comparison (`<`, `<=`, `>`, `>=`) and the signed
  divider/`srem` refuse an `Unknown` sign. `==`/`!=`, `+`, `&` and the rest do
  not read the sign, so they still compute.
* `overflow_pred` -- an `Unknown` sign has no sound predicate, so it returns
  `None` and the path is reported unmodelled rather than proved.
* `try_intrinsic` -- `sdiv`/`srem` on an `Unknown` sign are refused.
* `Rvalue::Cast` -- an `Unknown` *source* sign refuses the cast. This is the
  `-1i8 as i16` bug's home; zero-filling a signed source and sign-extending an
  unsigned one are both wrong, so neither may be guessed.

The sign travels with the seed too: `FieldEnv::seeds`, `len_seeds`, `elem_seeds`
and the `Indexed` element store all carry it, so an array element read out of the
store is a signed value on an `&[i8]` without any site having to look the type up
again. `operand_signedness` is *deleted* -- the lookup it performed no longer has
a caller to get wrong, because the sign is a field of the value it describes.

The regression net is the corpus (`signed_const_left_false`, `widen_signed_false`,
`signed_mul_negative`, `ashr_signed_false`) plus the two new entries
`signed_slice_element_is_signed` / `signed_slice_element_tripwire`, which pin the
element-side case: `i8::MIN` is the most negative `i8` and the largest `u8`, so
`xs[0] < 0` proves the opposite branch under the unsigned reading. A unit test
(`a_comparison_on_an_unprinted_sign_is_refused`) pins the refusal directly.

**Stage 2 — close the remaining `Rvalue` gaps, one at a time, each with a
tripwire.** The list below was written from reading the `Rvalue` enum, before
measuring which variants real rustc actually *prints*. Measuring first changed it:
two of the six items were not gaps at all, and the real ones were smaller and
differently shaped than the enum suggested. The lesson is the same one the
signedness round taught -- a gap list inferred from a type is a hypothesis, and
the corpus is the experiment that tests it. (`examples/mir_coverage` takes an
optional file argument, which is what made the measurement cheap.)

* **`Rvalue::Cast` to `bool` — not a gap.** `a as bool` does not compile
  (`E0054`: `cannot cast u8 as bool`); the idiom is `a != 0`, which lowers to
  `Ne`, already modelled. Nothing to do, and the item was removed rather than
  implemented.
* **`Rvalue::Len` — not a gap.** Modern rustc does not print `Len(` at all: a
  `.len()` lowers to `PtrMetadata`, and `grep -c 'Len('` over a full dump is `0`.
  The real work was in `PtrMetadata`, below, not in the variant the enum names.
* **`Rvalue::Struct` for a struct literal — DONE.** `Config { lo, hi }` is a
  *struct-literal* rvalue, not an array/tuple `Aggregate`. The two write different
  stores: an aggregate writes `Proj::Index` (tuple components, which a contract
  cannot name) and a struct literal writes `Proj::Field` (which a contract *does*
  name, as `c.lo`). The fields are printed in **declaration** order, which is the
  order the `Field(N)` projections count in, so a positional store is sound -- and
  the tripwire pins exactly that: `struct_literal_order_tripwire` writes `hi`
  first and must be refuted with a witness that is the `hi` operand, not `lo`.
* **`Rvalue::Ref` and dereference — DONE.** `&place` records the place it
  addresses, and `Env::resolve` rewrites a `*_2` whose `_2` is addressed into that
  place. This is a *substitution*, so a write through the reference and a read of
  the target meet in one store: `reference_write_reaches_target` verifies because
  the write is seen, and `reference_write_tripwire` fails because a snapshot model
  would have proved it. The same store fixed a parser bug: `strip_annot` stripped
  the parentheses off a bare `(*_2)`, leaving `*_2`, which no place parser reads.
* **`PtrMetadata` of an unsized array — DONE.** `a.len()` on `a: [u8; 4]` lowers
  to `_3 = &_1; _2 = _3 as &[u8]; PtrMetadata(_2)`. The reference-to-reference
  cast carries the address across, and `PtrMetadata` follows it to the array,
  whose length is the *type's constant* -- not a fresh variable, so `a.len() == 4`
  has something to agree with. `Env::pointee` is the one-level value step that
  `resolve` deliberately does not take, because metadata belongs to the pointee,
  not the pointer.
* **A whole-struct reassignment — DONE.** `c = d` copies a value the frontend
  models as its *parts*, so `Env::copy_parts` moves the field/element/payload/tag
  maps. It reports whether anything moved, which is what lets `set` keep the parts
  (the same `Val::Agg` convention an aggregate literal uses) instead of clearing
  them. `struct_reassign_then_field_read` moved from *incomplete* to **refuted**:
  the false contract is now a counterexample, not a shrug.
* **`Rvalue::Discriminant` and `Downcast` for a real enum match — DONE.**
  A `match` on an enum lowers to `_2 = discriminant(_1); switchInt(move _2)`,
  so the tag is a symbolic input whose *domain is the set of variant
  discriminants*. That bound is a fact about the type, not an assumption about
  the caller, so the run may assume it -- and it is what makes the `otherwise`
  arm (lowered to `unreachable` for an exhaustive `match`) genuinely unreachable
  instead of a spurious panic. Three pieces make it work:
  - `spec::EnumDef` / `EnumLayout` carry each variant's **discriminant** from the
    same source pass as the contracts, so a `(base as Variant)` downcast's tag
    and a contract's `Mode::Run` constant agree by construction rather than by
    convention. The discriminant is rustc's value, not the vector position: an
    explicit `B = 3` renumbers `C` to `4`, and numbering by position would put a
    contract naming `Gap::C` on the wrong tag. A one-line body
    (`pub enum E { A, B }`) and a multi-line one are read by the same
    top-level-comma split, so the numbering cannot drift between them.
  - `FieldEnv::bind_enum` binds the argument's own name to the tag, so a
    contract writes `m == Mode::Run`; each variant's first payload is bound
    separately (keyed by discriminant), so `m.Data` names the same variable the
    body's `((_1 as Data).0)` downcast reads.
  - `Seeds::tag_seeds` seeds the tag with its discriminants and
    `Seeds::payload_seeds` the payloads, and the run conjoins the *disjunction of
    the discriminants* onto the initial path -- `tag < count` is only the same
    domain when the numbering is `0..count`, which an explicit discriminant
    breaks.
  The tripwires pin the model rather than its presence: `enum_match_tripwire`
  claims every arm returns `2` and must be refuted with the tag in the witness
  (a constant tag would prove it), `enum_explicit_discriminant_tripwire` claims
  the `B` arm ran for `Gap::C` and must be refuted (a positional reader proves
  it), and `enum_payload_tripwire` names a *unit* variant's payload, which is
  refused rather than bound to a fabricated value. A variant with no payload is
  refused with a message naming the variant.
* **A locally constructed variant has a *known* tag — DONE.** `let m = Mode::Idle;`
  lowers to `_1 = Mode::Idle;`, a bare path constant with **no `const ` prefix**,
  which the rvalue parser did not recognise: it fell through to `Rvalue::Unknown`
  and the tag was never written, so `let m = Mode::Idle; match m` stayed
  `incomplete` even once a tag read from an *argument* worked. Two changes close
  it. `parse_rvalue` recognises a bare `Enum::Variant` path as a constant, and
  `eval_rvalue::Use` resolves it against the program's enum layouts -- the same
  table a `match`'s downcast reads -- writing a *constant* tag rather than
  seeding a symbolic one. The tag's width is the enum's *discriminants'*, taken
  from the destination's type, not the dump's `isize`: `Env::tag_widths` records
  it so `discriminant` reads the tag back at the width the contract's comparison
  was checked at. A payload construction (`Msg::Data(9)`) is `Rvalue::Variant`:
  the tag is the variant's discriminant and the operands are written as the
  variant's fields, so the match's `((_1 as Data).0)` downcast reads what the
  construction wrote. `enum_constructed_locally` verifies and
  `enum_constructed_locally_tripwire` is refuted; the payload case
  (`enum_constructed_payload_reads_through`) verifies.
* **A variant's tag is rustc's *discriminant*, not its position — DONE.** The
  reader used to number variants by their position in the declaration
  (`EnumDef::index_of` returned the vector index, the tag's width was the
  variant *count*'s, and payloads were keyed by position). An explicit
  discriminant breaks all three: `pub enum Gap { A, B = 3, C }` gives `C` the
  discriminant `4`, so a positional reader calls it `1`, puts a contract naming
  `Gap::C` on the wrong tag, and -- because the `match` arm constants come from
  rustc -- lets the contract and the arm disagree, which is a **false proof**
  (`enum_explicit_discriminant_tripwire` was *verified* before the fix). The
  data model now carries `(name, payload, discriminant)` per variant,
  `parse_discriminant_literal` reads a decimal/hex/binary/octal literal (an
  unreadable one refuses the *whole* layout rather than guessing), `tag_width`
  is the largest discriminant's width, the tag's assumed domain is the
  *disjunction of the discriminants* rather than `tag < count`, and payloads are
  keyed by discriminant. Two related built-in hazards were closed at the same
  time: a *declared* layout now wins over the built-in `Option`/`Result`
  numbering for a qualified name (`Shadow::Some` is tag `0` for a user
  `enum Shadow { Some, None }`, not `Option`'s `1` --
  `enum_user_variant_not_option_constructed_tripwire` was verified before this
  fix), and a qualified name whose enum is unknown is refused rather than
  answered by another layout that happens to share the variant name.
* **`// MIR FOR CTFE` is a copy, not a second function — DONE.** Building a
  tuple-variant constructor in a `let` (`Msg::Data(9)`) makes rustc print a
  *second*, `// MIR FOR CTFE`-marked body for the constructor. It is a copy of an
  item already printed above it, and the typed MIR has one body per item, so
  parsing it made the text side count 69 functions where `rustc_public` counted
  68 -- a `rustc_public` MIR-oracle failure (gate 9) over a function that is
  really there once. The parser now skips a `// MIR FOR CTFE` marker and the body
  that follows it. This is exactly the class of printer change gate 9 exists to
  catch: the frontend's own verdicts were unaffected, and only the oracle
  noticed.
* **`Rvalue::Unary(Not)` on a word operand** is handled, but `!x` is
  `all_ones ^ x` only when `dest_w` is the operand's width; assert the width
  rather than trusting `dest_w`. Small, and not yet measured against the corpus.

Corpus coverage went from 33/51 to 44/67 decided across this round; the new
entries are `struct_literal_reads_its_field`, `struct_literal_order` (+ its
tripwire), `reference_reads_through`, `reference_write_reaches_target` (+ its
tripwire), `array_len_is_the_type_constant`, `struct_reassign_reads_new_field`,
the five enum entries (`enum_match_is_bounded`, `enum_match_selects_by_tag`,
`enum_payload_reads_through` and their tripwires) and the two construction
entries (`enum_constructed_locally` + tripwire,
`enum_constructed_payload_reads_through`).

**Stage 3 — the contract language's two deliberate refusals.** `xs[i]` with a
symbolic `i` on a *slice*, and `a[k]` where `k` is a local rather than an
argument. Both halves are DONE.

*The local half is DONE.* `let k = i; a[k]` was refused because the contract's
`k` resolved to nothing. The refusal was misdiagnosed as "there is no local":
`rustc` prints no local for `k` at all. A `Copy` argument copied into a `let`
lowers to the argument's *own* local, and `k` survives only as a scoped
`debug k => _2;` — the body's `a[k]` really is `_1[_2]`. So the fix is to resolve
the name, not to bind a new variable.

The parser keeps every `debug` binding in `MirFn::debug_aliases` (the existing
`local_names` map cannot: it keeps the *first* binding per local, so that a scoped
alias does not rename the parameter, and it therefore drops `k`). `MirFn::
alias_locals` then decides which of those names may resolve, and it resolves a
name only when the aliased local is an argument, is never written by the body, is
not already an argument's own name, and does not alias two different arguments.
The `written` set is collected from the parsed blocks, so a `mut i` that the body
reassigns makes `k` unresolvable — the conservative direction, which loses a
proof rather than inventing one.

The names flow through `arg_vars` and `signed_args`, so `a[k]` builds the same
ite chain `a[i]` would *and* a signed `i` makes `k` signed in a comparison. Two
corpus entries carry it — `array_local_index_through_alias` (verifies) and
`array_local_index_tripwire` (must fail, and its witness pins `k` to a real index)
— and `array_local_index_written_refused` pins the `written` gate. Coverage went
from 44/67 to 45/69.

*The slice half is DONE.* The design note below had a soundness hole and it is worth
recording, because the hole is the interesting part.

A slice's length is a symbolic input, so `xs[i]` cannot be enumerated over a type
length the way an array can. The note proposed enumerating `0..MAX_INDEX_CHAIN` and
guarding each step with `k == n && k < len_var`, with the obligation that the
precondition imply `i < xs.len()`. That obligation is *not enough*. The chain has to
return something for `i >= MAX_INDEX_CHAIN`, and an index in `[64, len)` is in range
and past the enumeration, so it would fall through to a wrong element. The obligation
that closes it is on the *length*: `xs.len() <= MAX_INDEX_CHAIN`, which makes the
enumeration cover every index the slice can hold, not just the one the contract named.
Bounding the index alone leaves the body's read at some other index unmodelled.

So a slice's subscript has two obligations, not one, and they are checked separately so
the refusal names the missing one:

* `i < xs.len()` — the named index is in range.
* `xs.len() <= MAX_INDEX_CHAIN` — the enumeration covers the whole slice.

The machinery: `IndexBound` (`Const(n)` for an array, `Len(v)` for a slice) replaces the
`u64` that `index_guards` used to yield, so the bound travels as one shape whether it is
a constant or a term. `FieldEnv::sym_bound` records it; `bind_sym_index` enumerates
`steps` accordingly. On the executor side a slice's chain length cannot come from
`fixed_len` (there is none), so `Seeds::slice_steps` carries it — and it is populated
*only* when the contract established `len <= MAX_INDEX_CHAIN`, which is what keeps a
slice subscript a refusal when it is not bounded. `Indexed` gained `slice_steps` and
`index_chain` now takes `fixed_len.or(slice_steps)`.

Three corpus entries carry it and each pins a different half: `slice_symbolic_index`
(verifies, both bounds present), `slice_symbolic_index_tripwire` (must FAIL on the
postcondition, with `i` pinned non-zero — the evidence the chain depends on the index),
and `slice_unbounded_length_refused` / `slice_unbounded_index_refused` (each supplies one
bound and withholds the other, so a rule checking only one would model what it must
refuse). The tripwire names `xs[i]` *and* `xs[0]`: naming only the literal leaves the
body's symbolic read unmodelled and the entry comes back a refusal rather than a
refutation, which a `!is_verified` assertion would accept for the wrong reason — so the
test asserts `Failed`, not `!is_verified()`.

One shape is left out on purpose. A body reading a *different* symbolic index than the
contract bounded (`xs[j]` under a contract about `xs[i]`) is modelled, but with two
64-deep chains the engine returns `Unknown` rather than a refutation, so it is a
completeness cliff and not a corpus entry: an entry that neither verifies nor refutes is
not evidence. Coverage went from **51/82 to 52/85** and the test count from 488 to
**490**.

A second boundary is a consequence of the design and worth stating: a slice's chain
exists only when the *contract* bounded the length, because `sym_bound` is what the
executor's `slice_steps` is derived from. So a function whose body reads `xs[i]`
symbolically but whose contract never names a slice subscript gets no chain and that read
stays a refusal. An array does not have this coupling — `array_lens` comes from the type,
not the contract — so a body-only symbolic array read is modelled where the slice one is
not. The asymmetry loses a proof rather than inventing one, and closing it would mean
walking the body for slice reads and then proving `len <= 64` for functions that never
needed slice modelling, so it is left as the honest boundary.

**Stage 4 — the missing intrinsics.** `wrapping_neg`, `wrapping_div`,
`wrapping_rem`, `leading_zeros`, `trailing_zeros`, `count_ones`, `pow`. The
`wrapping_*` family is the same arithmetic the `checked_*` arms already do, minus
the overflow obligation, so it is mostly plumbing. `count_ones` and the zero-counts
are small bit-vector loops and belong in `discharge-arithmetic` beside the other
proved primitives, not in the frontend. All of these are now modelled except `pow`
and the division families that cannot express a zero divisor as a value (see below).

**Stage 4 progress: the two-operand families and the whole unary surface are
modelled.** `checked_*`, `saturating_*`, `wrapping_*` and `overflowing_*` are all
computed in the frontend from their operands: the two-operand `overflowing_*`
shapes share the `failure` predicate the other families read, and were checked
against `core` over the whole `u8`/`i8` domain. `count_ones`, `leading_zeros` and
`trailing_zeros` are the bit counts; `neg` and `abs` are modelled in all four
families. The `Intrinsic` enum was restructured to say so: `Bits(BitKind)` for the
counts, `Unary(Family, UnOp)` for the operators, and `Overflowing(BinOp)` for the
`(T, bool)` family. Findings worth more than the coverage:

* **`count_ones`, `leading_zeros` and `trailing_zeros` are the modelled calls whose
  result width differs from their operand's** (`u8::count_ones` returns `u32`). The
  model builds the count at the operand's width and zero-extends it to the
  destination's; the executor reads the destination's width for exactly this reason,
  and the `eval` signature takes the operand width and the result width separately.
  Every other shape passes the same value for both, so the change is inert outside
  these three.
* **`saturating_neg` and every `abs` do not exist on the unsigned types**, while
  `wrapping_neg`, `checked_neg` and `overflowing_neg` do -- where negation is modular
  and the failure case is `x != 0`. So `is_modelled` reads the sign for the unary
  operators rather than assuming one, and the unsigned `neg` families are modelled
  rather than refused. This is the one place the four families have different
  *membership*, not just different definitions.
* **`MIN` is where the four families separate, and the model has no `MIN` special
  case anywhere.** `neg` and `abs` share the `0 - x` core; `wrapping_*` return `MIN`
  there because `0 - MIN` wraps, `saturating_*` clamp to `MAX` through the same
  overflow predicate, `checked_*` return `None` through it, and `overflowing_*`
  report it as the flag. One expression plus one predicate, four answers -- so the
  four cannot drift apart.
* **An off-by-one in `leading_zeros` was caught by the exhaustive walk.** Counting
  `x < 2^k` from `k == 1` reports `w - 1` for `x == 0`, where `core` reports `w`.
  That is one wrong input out of `2^w`, and it is exactly the input the corpus
  tripwire names -- a sample-based test would have missed it.

* **The `overflowing_*` return is a `(T, bool)` whose components a modelled call
  writes *field by field*, and the `ret.N` reader had to learn that.** A literal
  `_0 = (a, b)` stores components under `Proj::Index`; a modelled call writes
  `_0.0`/`_0.1` under `Proj::Field`. `Env::get` already met both spellings, but two
  other readers did not: the return-component collector read `elems` only, and
  `Env::get` itself returned `Unknown` early for a local with no whole value before
  ever consulting the projected store. The symptom was a `ret.1` contract refused as
  "the return type is an aggregate, so `ret` has no single value" -- a message about
  the wrong problem, since the answer was to read the component, not to give up on
  it. Both readers now go through `get`.
* **`overflowing_div`/`overflowing_rem` panic on a zero divisor and are refused.**
  The flag reports `MIN / -1`, which makes the family look like a total form of
  division -- and the previous session modelled it as one. A differential test
  against `core` is what exposed it: `7u8.overflowing_div(0)` *unwinds*, it does not
  return `(_, true)`. So the flag is not the whole failure predicate, and treating
  the call as total would have let a function that divides by zero be *proved
  panic-free*. `is_modelled` now admits only `checked_div`/`checked_rem`, and the
  corpus records why.

`wrapping_div`/`wrapping_rem`/`saturating_div`/`saturating_rem` are *not* reachable
by design, because they panic on a zero divisor and modelling them as total would
hide that panic; `overflowing_div`/`overflowing_rem` join them for the same reason.
`pow` remains reachable and unmodelled. The bit-count proofs do **not** go in `discharge-arithmetic`: their oracle here is Rust's own method, checked
exhaustively over the whole operand domain, which is a stronger oracle than a
small-domain enumeration would be. A third engine with less coverage is not a proof,
so the split the roadmap proposed is not made.

**Ordering rationale.** Stage 1 first because it is the *class* of bug, not one
bug; doing Stages 2–4 first multiplies the call sites that can forget the sign.
Stage 2's enum item before Stage 3 because an enum match appears in almost every
real function and the slice-index case appears in almost none. Stage 4 last
because it is additive coverage with no soundness content.

**Standing tripwire rule for every stage.** A new shape is not "supported" until
there is a corpus entry that *verifies* and a tripwire that *fails*. The tripwire
is the evidence: a shape that only ever verifies is a shape whose model has never
been contradicted.

## Ferrocene gate: what was verified end to end

The Ferrocene work landed as three commits on `license-arith-mir-oracle` (PR #3):

- `af8818e` — the gate itself: `tools/ferrocene/run.sh` (exit 0 built / 1 real failure /
  2 no toolchain), `criticalup.toml`, `tools/ferrocene/README.md`, gate 3 in
  `scripts/gate.sh`, and the `ferrocene` job in `.github/workflows/ci.yml`.
- `18681e1` — `examples/bare_metal.rs`, the `#![no_std]` `lib` example that *calls the
  decision procedure*, so the qualified compiler builds the prover itself and not just the
  types around it. Wired into gate 4 and `run.sh`; `test = true` so the host verdict tests
  actually run. Test count 463 -> 466.
- `5bed9d4` — the token goes to CriticalUp on stdin, not as an argument, so it never
  reaches the process table.

Verified, not assumed:

- Full `scripts/gate.sh`: **12/12 green** on the final head.
- `run.sh` exercised in all three modes: no toolchain (exit 2, reports and skips), stable
  rustc named via `FERROCENE_RUSTC` (exit 0, all three builds), bad path (exit 2).
- `examples/bare_metal.rs` builds for `thumbv7em-none-eabihf` with `--no-default-features`,
  and its three host tests pass (proved / refuted / refused).
- `actionlint` clean on `.github/workflows/ci.yml`.
- CI on `5bed9d4`: **all seven jobs success**. The `ferrocene` job ran and reported its skip
  rather than passing quietly — steps 5 and 6 `skipped`, step 7 emits the `::warning::`
  annotation, log reads "No FERROCENE_TOKEN secret; skipping the qualified-toolchain build.
  This is reported, not passed: the gate did not run." The token is masked (`token: ***`).

`cargo test --workspace` *without* `--features std` fails in `src/smt.rs` lib tests
(`std::panic::catch_unwind`). That is pre-existing — confirmed identical on a stashed tree —
and this repository only ever runs tests with `--features std`.

What Ferrocene does *not* buy, stated in the README, the tool's README and here: a qualified
compiler is not a qualified verifier, and `discharge`'s engine is outside Ferrocene's
qualification scope. The gate checks the qualified compiler accepts the sources unchanged.

## Stage 3, first half: a contract may name a local that aliases an argument

The roadmap's Stage 3 listed two refusals. The smaller one — `a[k]` where `k` is a
local — turned out to be a misdiagnosis, and the misdiagnosis is the interesting
part.

The entry was documented as "there is no variable to build a chain for `k`", with
`k` assumed to be a local the contract language could not reach. rustc prints no
local for `k` at all. `let k = i;` where `i: usize` is `Copy` lowers to *no
instruction*: `a[k]` is `_1[_2]`, and the name `k` survives only as a scoped
`debug k => _2;` inside `scope 1`. So the body already used the argument as the
index; only the contract text had `k`. The fix is to resolve the name, not to bind
anything.

**The parser could not see it.** `MirFn::local_names` keeps the *first* `debug`
binding per local, and that rule is load-bearing: a scoped `debug s => _1;` after
`let s = a;` would otherwise rename the parameter `a` to `s`, and a contract
saying `a <= 127` would find only `s` and be skipped. Keeping the first binding is
what makes `a` keep meaning `a`. But it means the scoped binding for `k` is
dropped, so `k` reached the contract parser as nothing.

`MirFn::debug_aliases` now keeps every binding, in printed order, and
`MirFn::alias_locals` decides which ones may resolve. A name resolves only when
all four hold:

* the aliased local is an argument — never a temporary;
* the body never writes that local;
* the name is not already an argument's own name, so an alias cannot shadow a
  parameter; and
* the name does not alias two different arguments.

The `written` set is collected from the *parsed blocks* rather than from the text,
so it is the parser — which alone knows which lines became statements — that
decides. This is what makes the rule sound on the dump alone rather than on an
assumption about what rustc prints today.

**The divergence case, measured.** `let k = i; i = 2;` does *not* print
`debug k => _2;`. rustc materialises a real local (`let _3: usize;`) and prints
`debug k => _3;`, so `k` is not an argument alias and is refused — correctly, and
for a reason the frontend can see rather than one it has to be told. The
`written` check still has to exist for the case where rustc *does* print the
alias against a written argument, which is a dump shape this frontend must not
trust. A parser-level unit test constructs exactly that dump and asserts the name
is withheld, so a refactor cannot drop the check unnoticed.

**Sign flow.** The alias names go into both `arg_vars` and `signed_args`. The
second matters as much as the first: a signed `i` aliased as `k` must make `k < 0`
a signed comparison, which is the class of bug the three-case `Sign` type exists
to prevent.

**Evidence.** `array_local_index_through_alias` verifies and
`array_local_index_tripwire` fails with a witness that pins the index — which only
happens if `k` resolved to the real index variable. `array_local_index_written_refused`
pins the divergence gate. Two parser unit tests pin the alias rule and the
`written` gate with no nightly needed. Coverage went from **44/67 to 45/69**, and
the test count from 466 to **470** (two parser unit tests, one integration test,
and the renamed corpus entries). Full `scripts/gate.sh`: **12/12 green**.

The slice half of Stage 3 landed in the same branch. Its own section above records the
soundness hole the original roadmap note had — an index-only bound is not enough, because
the chain must be exact for *every* index the slice holds, which needs `len <=
MAX_INDEX_CHAIN` as a second obligation — and the machinery that closes it.

## Stage 3 — enum discriminants are rustc's values, not declaration positions

The enum model numbered variants by their position in the declaration. That is
right for the common case and wrong the moment the source gives an explicit
discriminant, and the wrongness is a *false proof* rather than a refusal, because
the `match` arm constants come from rustc while the contract's variant constant
came from this reader.

**The bug, measured.** `pub enum Gap { A, B = 3, C }` gives `C` the discriminant
`4`. The reader dropped the `B = 3` line (it matched no known shape), so its
layout became `[A, C]` with `C` at position `1`. A contract `requires: g ==
Gap::C` then pinned the tag to `1`, the body's `switchInt` compared against the
real constants (`0`, `3`, `4`), and the contract landed on the `B` arm. The
tripwire `enum_explicit_discriminant_tripwire` — which claims the `B` arm ran —
was **verified**, i.e. a false contract proved. Before the fix the corpus read
`decided 46 of 74` with both new tests failing; after, `49 of 78` with both
refuted.

**Three places carried the position, and all three moved to the discriminant.**
`EnumDef.variants` is now `(name, payload, discriminant)` and `index_of` returns
the stored discriminant; `tag_width` is the largest discriminant's width (three
bits for `4`, not the two a count of three gives); and the tag's assumed domain
is the *disjunction of the discriminants* rather than `tag < count` — because an
assumed bound that is *false* for a real input is the unsound direction, it can
make a proof vacuous. Payload seeds are keyed by discriminant too, matching what
a `Downcast` projection carries.

**An unreadable discriminant refuses the whole layout.** Only a literal is read
(decimal, `0x`/`0b`/`0o`, optional type suffix). `B = 1 << 4` is not evaluated:
dropping the variant would shift every later discriminant and guessing one would
put a contract on the wrong tag, so the enum is dropped from the map entirely and
a contract naming any of its variants becomes a refusal. The literal reader
requires the *whole* remainder to be digits, so `1 << 4` is refused rather than
silently read as `1`.

**Two built-in hazards closed at the same time.** A qualified name
(`Shadow::Some`) now resolves against the *declared* layout first, so a user
`enum Shadow { Some, None }` is not mistaken for `Option` — pre-fix,
`enum_user_variant_not_option_constructed_tripwire` was **verified** because the
built-in `Option` numbering put `Some` on tag `1`. And a qualified name whose
qualifier is not a declared enum *and* not one of the two built-in enums
(`Option`, `Result`) is refused rather than answered by another layout that
happens to share the variant name. (The built-in case is the follow-up in the
next section: a qualified `Option::<u8>::Some` must still resolve, and a
declared layout must still win over it.)

**Evidence.** Four corpus entries: `enum_explicit_discriminant_selects_by_tag`
(verifies) with `enum_explicit_discriminant_tripwire` (refuted), and
`enum_user_variant_not_option` / `..._constructed` (verify) with their two
tripwires (refuted). Eight unit tests pin the parser and the layout reader with no
nightly needed, plus two integration tests pinning the earlier array-spelling
work. Coverage went from **45/69 to 49/78**, the test count from 470 to **480**.

## Stage 3 follow-up — three reader bugs a review found after the discriminant landed

The discriminant work above fixed the *value* a variant has. Three defects in the
same reader survived it, and all three fail in the same direction: a function
that should have been checked is instead dropped from the check set or refused,
and the user is never told. They were found by review, then reproduced against the
real code before anything was changed.

**1. A refused one-line enum swallowed everything after it.** `enum_head` returns
the parsed head of an `enum` line. For a one-line body whose discriminant is
unreadable (`pub enum E { A, B = 1 << 4 }`) it returned "a multi-line body
follows" — but the closing brace was already on that line. The caller then opened
an enum *cursor*, and every following line, including `///` contracts and the `fn`
items they belong to, was consumed as enum contents. Those functions had no
contract at all, so they were neither verified nor reported as skipped: they
silently left the check set, which is the worst failure mode a verifier has. The
head is now a three-way enum — `Inline(variants)`, `MultiLine`, `Refused` — and
`Refused` drops the layout *without* opening a cursor. The multi-line path already
closed its cursor at the brace; the one-line path now does too.

**2. A qualified standard construction resolved to nothing.** rustc prints a
standard construction with its generic arguments: `let o: Option<u8> =
Option::<u8>::Some(9)` lowers to `_1 = Option::<u8>::Some(const 9_u8)`. The
qualifier branch split the name on `::`, so the segment before the variant was
`u8` — the generic argument, not the enum — and `enums.get("u8")` found no layout.
The construction became an unmodelled read and the `match` an *unmodelled switch
discriminant*, losing a shape the unqualified spelling (`Some(9)`) handles. The
fix strips balanced `<…>` generic arguments before splitting, so the qualifier is
`Option`. Since no source file declares `Option` or `Result`, those two qualifiers
now resolve to the fixed numbering (`Some`/`Err` = 1, `None`/`Ok` = 0), but only
*after* a declared layout has had its chance — so a user `enum E { Some, None }`
still wins over `Option`'s numbering.

**3. A trailing line comment erased the whole enum layout.** `B = 3, // special`
puts the comma *before* the comment. The variant reader trimmed a trailing comma
off the raw line, but the line now ends in the comment, so no comma was trimmed
and `3, // special` went to the discriminant reader, which rejected it — and a
rejected discriminant drops the *entire* layout. Every contract naming a variant
of that enum then became a refusal. The comment is not part of the variant, so it
is stripped first, with string and character literals tracked so a `//` inside one
is not mistaken for a comment.

**Evidence.** Four corpus entries: `option_qualified_some_payload` and
`enum_trailing_comment_keeps_the_layout` (verify) with their tripwires (refuted),
plus six unit tests and two integration tests. Coverage went from **49/78 to
51/82**, the test count from 480 to **488**. Each fix was checked for teeth by
reverting it and watching its test fail: without fix 1 the contract after a
refused enum is gone (`by_fn` is empty); without fix 2 the qualified construction
is `incomplete (1 reason) - unmodelled switch discriminant`; without fix 3 the
layout is dropped and the contract is `skipped: unknown name`.

## Toolchain — edition 2024 and the MSRV floor (1.85)

Both manifests are **edition 2024** with `rust-version = "1.85"`. The two numbers
are one decision, not two: cargo refuses edition 2024 on any compiler below 1.85,
and 1.85 is the release that stabilised it, so there is no version that takes the
edition without the floor. Raising one means raising the other.

The floor is a *lower* bound, not a pin. The crate is exercised on current stable
(1.99 at the time of writing) and the MIR frontend runs a nightly. The oracle
toolchains move independently and none of them forces the floor down: Verus tracks
stable (`channel = "1.99.1"`), Kani tracks a nightly (`nightly-2026-10-23`), and
Ferrocene — the qualified compiler, whose lag is the only one that could matter
for a safety build — is downstream of Rust 1.96. The MSRV is deliberately *not*
raised to follow them: a `no_std` crate that ships into a bare-metal safety build
is the one place a high floor costs something real, because it locks out qualified
and long-term-support toolchains that lag upstream.

**The migration was three edits, all found by compiling rather than by reading:**

1. `examples/verusdiff.rs` — `filter(|(_, &l)| …)` is rejected in edition 2024
   ("cannot explicitly dereference within an implicitly-borrowing pattern"); it
   becomes `filter(|&(_, &l)| …)`.
2. `tests/loopdiff.rs` — `gen` is a reserved keyword in edition 2024, so `fn gen(`
   was renamed to `fn make_steps(`.
3. `discharge-arithmetic/src/prove.rs` — three `.map_or(true, |c| …)` calls became
   `.is_none_or(|c| …)`. This one is *caused by the MSRV bump*, not by the
   edition: clippy only suggests `is_none_or` (1.82+) once `rust-version` permits
   it, so the lint appears exactly when the floor moves. Worth knowing before
   touching `rust-version` again.

**The floor is now a gate, not a claim.** `scripts/gate.sh` step 13 builds with
`1.85` (overridable via `DISCHARGE_MSRV`) so a feature newer than the floor fails
in CI rather than in a downstream build. It follows the Ferrocene/Kani convention:
an absent toolchain, or a `thumbv7em-none-eabihf` target not installed *for that
toolchain*, is reported and skipped rather than folded into a pass. CI installs
both the 1.85 toolchain and that target for it so the gate actually runs. The gate
numbering is now **13 steps**, not 12; the README and `ci.yml` were renumbered
with it.

## The bit-blaster walked a DAG as a tree, and no budget noticed

`wrapping_pow` at a *symbolic* exponent hung. Not slowly: the query never returned, so
`prove` printed no verdict at all, which the previous section already established is worse
than any verdict. The shape is small -- `u4`, one base variable, one `u32` exponent -- and
the arena stayed nearly empty, so nothing in the existing guards fired.

The cause is a mismatch between how the term is *built* and how the blaster *walks* it.
`pow` is a 32-step fold, and every step rebuilds the running product from the same shared
subterms, so the term is a DAG with heavy sharing. `blast` recurses as if it were a tree:
it visits a shared subterm once per path to it. For a 32-step fold that is up to 2^32 paths
through a graph of a few hundred nodes. Instrumenting the walk confirmed it directly --
u4 needed **more than 10^8 visits** to finish, and the count was identical for the BDD pass
and the SAT pass because both recurse the same way. That is not a slow answer; it is a hang,
and the query never reaches the code that would have fallen back.

Two plausible explanations were checked and were wrong before the right one landed:

1. **"The arena overflows."** No. The `overflow` guard at the top of `blast` was added for
   exactly this fold, but it fires on a *full* node table, and this walk fills nothing --
   it recomputes. Measurement showed `overflow == false` throughout.
2. **"The SAT fallback will finish it."** No. The fallback has the same tree-walk recursion
   over the same DAG, so it hangs identically. A BDD-only memo was tried first and *still
   hung on `u8`* -- the BDD pass stopped (correctly, via its arena cap) and the SAT pass
   then hung, with no bound of its own. That is what put a budget on *both* passes; it was
   only visible by measuring each pass separately.

The fix has two parts, and they are not redundant:

- **A memo on the BDD pass** (`BLAST_MEMO_N` slots in `Ctx`). A hit collapses the paths:
  the same u4 query drops from more than 10^8 visits to **540**. It is keyed by the term id
  *including* its generation bits, so the arena reset that recycles slots also invalidates
  the memo -- no clearing pass, and a stale key can never match a current term. This is the
  half that buys *capability*: without it a `pow` at any width answers `Unknown`, because
  the budget below stops the walk before it finishes.
- **A step budget on both passes** (`MAX_BLAST_STEPS`). The memo is a cache, not a
  guarantee: a term whose working set exceeds the memo would evict its own entries and
  recompute. The budget bounds the *work*, and it is the part that makes "never hangs" true
  rather than likely. When it trips it sets the same `overflow` flag the arena cap sets, so
  the query degrades along the path that already exists -- BDD to SAT, SAT to `Unknown` --
  instead of inventing a new one. The SAT pass additionally calls `Cnf::mark_overflow`,
  because a step-truncated CNF must read as `Unknown`, never as a satisfiable one.

The SAT pass gets the budget but *not* a memo, and that asymmetry is deliberate. The BDD
memo's soundness is free: the arena is wiped by `with_fresh`, and the memo key carries the
generation, so a stale entry cannot match. The SAT blaster has no equivalent -- it appends
gates to a `Cnf` that is reset per query, and a memo of `Lit`s would have to reason about
whether those gate slots were reused. That is a real obligation, and measurement says it
buys nothing: a SAT memo changed no verdict, only the latency of the fallback (the same u8
query took ~80ms with it and ~860ms with the budget alone). So the budget alone carries the
SAT pass, and no cross-query cache does.

Measured after the fix: `u4` **Valid in ~34ms**, `u6` Valid in ~1.7s, `u8` **Unknown in
~80ms** -- all three *return*, and none is a wrong answer. `Unknown` at `u8` is honest: the
BDD diagram genuinely exceeds its cap there, which is the case the SAT fallback exists for,
and the fallback's own budget then declines rather than guessing.

The regression test is `a_symbolic_pow_returns_a_verdict_instead_of_hanging` in
`src/mir/intrinsics.rs`. It is *verified to hang without the fix* -- with both the memo and
the budget neutralised it ran past 90s and was killed -- which is the only thing that makes
it a regression test rather than a test that happens to pass. Two details matter: it uses a
*symbolic* exponent, because a concrete exponent unrolls the fold to one path and never
showed the blow-up; and it accepts `Valid` or `Unknown` but rejects a `Counterexample` or
`Unsat`, so it pins both termination and that the budget did not let a truncated encoding
masquerade as a complete one.

The size of the memo is a real constraint, not a free parameter. `Ctx` is already ~1.8 MB
and lives in a thread-local, so it sits close to the test harness's thread stack: growing it
by 512 KB overflows that stack. The memo is therefore small on purpose -- 128 slots, about
33 KB -- and the measurement says that is enough for the fold terms a single query touches
(`N=64` and `N=256` behave identically to `N=128` on the corpus).
