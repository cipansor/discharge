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

The five gates this crate depends on (clippy `-D warnings`, the test suite, the bare-metal
`no_std` build, the zero-dependency check, the z3 oracle) were five separate commands,
written in the README and copied into summaries by hand. That is exactly how a gate quietly
stops being run: the summary says "all gates green" because the four that were re-run were
green, and the fifth was recalled rather than executed. `scripts/gate.sh` is now the single
entry point, it fails on the first gate that does not hold, and it treats an unavailable z3
oracle as a failure rather than a pass.

This is the same lesson as the two tooling defects above, one level up: **a gate you did
not run is not a gate you passed**, and the only way to keep that honest is to make "run
all the gates" a single command whose exit code is the claim. A summary that says "gates
green" should quote that command's output, not a memory of running the pieces.

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

The README's "Layout" section drew `sparkrs/` as a tree. It had drifted from the
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
