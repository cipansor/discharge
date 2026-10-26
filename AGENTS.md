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
