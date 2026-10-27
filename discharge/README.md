# discharge — formal verification that lives inside the Rust code

> An experiment: what if Rust could carry its own proof tooling the way
> SPARK/Ada carries `gnatprove`? Not a plugin, not an external solver, not a
> nightly feature — a **bit-blasting decision procedure compiled into your
> artifact**, next to a Curry–Howard proof kernel and a contract vocabulary.

> **Not affiliated with AdaCore or SPARK.** "SPARK" and "SPARK Pro" are
> AdaCore's; `gnatprove` is their tool. This crate is an independent experiment
> inspired by the *shape* of that workflow — contracts in the source, proofs
> discharged by a tool — and it embeds its own decision procedure rather than
> wrapping theirs. It is not a port, a wrapper, or a supported AdaCore product,
> and the name was chosen to describe what the crate *does*, not where it comes
> from.

`no_std`. Zero dependencies. Fixed-size, heap-free arena. `#![forbid(unsafe_op_in_unsafe_fn)]`.

```rust
use discharge::prelude::*;
use discharge::sym::*;

// ∀ x:u8. (x & 0x0f) < 16          — proved by the embedded SMT engine
let proved = discharge::smt::with_fresh(|| {
    let x = var(8);
    (x & 0x0fu32).lt_val(16).prove().is_proved()
});
assert!(proved);
```

Run the flagship demo:

```console
$ cargo run --features std --example flight_control
[symbolic]  map_reading output bound       : valid (proved for all inputs)
[symbolic]  rate_limit step bound          : valid (proved for all inputs)
[exhaustive] clamp holds for all 65536     : true
[exhaustive] output in [PWM_MIN, PWM_MAX]  : true
[exhaustive] rate limit for all u8 pairs   : true
[exhaustive] mapping is monotone           : true
[kernel]    certificate accepted, value = 1500
[refuted]   raw < ADC_MAX is false, witness raw = 4095
[honesty]   (a*b)*c == a*(b*c) at 12 bits  : unknown (no conclusion: budget exhausted, ill-formed query, or stale handle)

all obligations discharged
```

---

## The idea in one paragraph

SPARK's advantage is not that Ada is a better language. It is that **the prover
is part of the toolchain and the contracts are part of the source**. Rust has a
superb type system and no such prover, so verification is outsourced to external
tools (Kani, Creusot, Prusti, MIRAI) that you must install, configure, and trust.
This crate asks what happens if you instead *compile the prover in*: lower
bit-vector formulas to **Reduced Ordered Binary Decision Diagrams**, which are a
canonical form, so two formulas are equivalent exactly when their diagrams are
the *same node*. That one property yields, with no external process:

| Query | Meaning |
|---|---|
| `prove(p)` | `p` holds for every input (diagram is the `true` node) |
| `find_model(p)` | a concrete satisfying input, or `Unsat` |
| `prove_implies(pre, post)` | `pre => post` holds for every input |
| `prove_equiv(a, b)` | `a` and `b` are equivalent for every input |

## The three ways this crate proves something

They are deliberately different tools, and each has a different honesty profile.

| # | Mechanism | Entry point | Complete? | Can it lie? |
|---|---|---|---|---|
| 1 | **Symbolic** — BDD, then CDCL SAT fallback | `smt::prove`, `sym::*::prove()` | no (scaling wall) | no — it returns `Unknown` |
| 2 | **Exhaustive** — every input of a real `fn` | `exhaustive::for_all_u8/u16` | yes, small domains | no |
| 3 | **Type-level** — Curry–Howard kernel | `proof::Certificate`, `assert_proof!` | yes, for composition | no — it will not compile |

A serious safety argument uses all three and says which one discharged each
obligation. That is what `examples/flight_control.rs` demonstrates.

## What is in the box

| Module | Contents |
|---|---|
| `smt` | Bit-vector terms, ROBDD engine, `Verdict`, counterexamples, `no_std` arena |
| `sym` | Operator overloading so specs read like code: `(x + y).eq(y + x).prove()` |
| `logic` | Checked/saturating arithmetic and a Q16.16 `Fixed` type, each with proofs |
| `proof` | Curry–Howard kernel (`Truth`, `And`, `Imp`, `Equals`) + composable `Certificate` |
| `contract` | Runtime `Pre`/`Post`/`Assert` over concrete values, structured errors |
| `vc` | `requires`/`ensures`/`invariant`, `verify_body`, `Verified<T>` |
| `wp` | Hoare logic: weakest preconditions, automatic VC generation, loop rules, termination by variant |
| `smtscript` | SMT-LIB2 export, so an external solver can check the same formula |
| `mem` | Bounded symbolic memory: `read`/`store`, frame condition, composes with `wp` |
| `quant` | Bounded `forall`/`exists`, expanded into finite conjunctions/disjunctions |
| `exhaustive` | Complete proofs by enumeration over `u8`/`u16` |
| `primitives` | Total integer ops and a refinement-typed `Bounded<MIN, MAX>` |
| `macros` | `verify!`, `verify_implies!`, `contract!`, `proof!`, `assert_proof!`, `check!`, `verify_exhaustive!` |

## Verification conditions are generated, not hand-written

`vc` lets you write an obligation by hand. `wp` derives it from the program, which
is the part that actually feels like SPARK: you state `requires` and `ensures`,
describe the body, and read a verdict *per rule*.

```rust
use discharge::prelude::*;
use discharge::smt::{self, var};
use discharge::wp::{self, Stmt};

let report = smt::with_fresh(|| {
    let sum = var(4);
    let i = var(4);
    let n = var(4);
    let step = var(4);

    let pre = smt::and(n.le_val(3), step.le_val(3));      // requires

    let init_sum = Stmt::Assign { var: sum, expr: smt::word(0, 4) };
    let init_i   = Stmt::Assign { var: i,   expr: smt::word(0, 4) };
    let bump_sum = Stmt::Assign { var: sum, expr: sum + step };
    let bump_i   = Stmt::Assign { var: i,   expr: i + 1u32 };
    let body     = Stmt::Seq { first: &bump_sum, second: &bump_i };

    // The invariant carries the arithmetic link; this is the human's job.
    let inv = smt::and(i.le(n), sum.eq(smt::mul(i, step)));
    let loop_ = Stmt::While { cond: i.lt(n), invariant: inv, body: &body };
    let prog = Stmt::Seq {
        first: &init_sum,
        second: &Stmt::Seq { first: &init_i, second: &loop_ },
    };

    wp::verify(&prog, pre, sum.le(smt::mul(n, step)))     // ensures
});

for ob in report.obligations.iter().flatten() {
    println!("{:?}: {}", ob.rule, ob.discharge());   // LoopPreserve: valid
}                                                    // LoopExit: valid
assert!(report.is_verified());
```

Run it: `cargo run --features std --example pipeline`.

Three things about `wp` are worth knowing, because each is a place where a naive
implementation quietly proves the wrong thing:

1. **The walk starts at the postcondition.** Backward from `post`, through the
   body, to a weakest precondition; the contract is `pre => wp(body, post)`.
   Starting from `pre` instead yields a vacuous condition that "verifies" almost
   anything.
2. **Loop obligations are universally quantified over the loop-head state.** They
   are recorded in loop-head terms and *not* rewritten by the assignments that
   dominate the loop. Rewriting them makes them trivially true whenever the
   initialisation pins the variables, which turns a broken invariant green.
   Assertions are the opposite: they are checked where control reaches them, so
   the dominating assignments *do* apply.
3. **Termination is proved separately, by a variant.** Hoare logic alone says
   "correct if it exits". Give the loop a `variant` and its progress is proved
   too, which upgrades the result from partial to total correctness.

### Termination: give the loop a variant

A `variant` is an expression in loop-head terms that must strictly decrease each
iteration. For an unsigned measure, `I && c => V' < V` is the whole rule: a
strictly decreasing sequence in a well-founded order cannot be infinite.

```rust
let loop_ = Stmt::While {
    cond: i.lt_val(10),
    invariant: i.le_val(10),
    variant: Some(smt::sub(smt::word(10, 8), i)),   // 10 - i decreases by one
    body: &step,
};
```

The value *after* one iteration is computed by symbolic evaluation of the body, so
you write the measure once, not twice. Through an `if` it becomes
`ite(cond, then_value, else_value)`; through a sequence it composes in execution
order. That is what makes a conditional body work without extra annotation:

```rust
// while i < 10 { if i < 5 { i := i + 2 } else { i := i + 1 } }
// V' is derived as ite(i < 5, 10 - (i + 2), 10 - (i + 1))
```

Because the measure is a bit-vector expression evaluated with wrapping, a measure
that wraps around is caught rather than silently accepted. Take the divergent loop
from `tests/wp.rs`, `while i != 0 { i := i + 2 }`: claim `variant: i` and the
obligation is refuted, because from `i == 253` the next value is `255`, which is
larger. The variant rule is what turns "this loop does not terminate" from a
comment into a failed proof obligation.

`Report::correctness()` tells you which claim you actually got:

```rust
assert_eq!(report.correctness(), Correctness::Total);    // every loop has a variant
assert_eq!(report.correctness(), Correctness::Partial);  // some loop does not
```

`Total` requires *every* loop to carry a variant. One unannotated loop makes the
whole report `Partial`, which is why the classification compares the number of
loops against the number of variants rather than checking that a variant exists
somewhere.

A report can be `Total` and still `!is_verified()`: the two questions — does it
terminate, and does it meet its contract — are answered independently.

### Why `variant_after` must havoc a nested loop

The variant obligation is `I && guard => V' < V`, where `V'` is the measure evaluated
after one iteration of the body. The whole proof rests on `V'` being the measure's *real*
value after that iteration, so `variant_after` must model the body's effect on the measure
faithfully. For an assignment, a sequence, or a conditional that is substitution and
`ite`. For a nested loop it is harder, because the loop runs an unknown number of times.

The first version read a nested `while` as a no-op — the measure "survives" it. That is
false whenever the inner body writes a variable the measure reads, and it is false in the
worst possible direction. Consider:

```text
while i < 100 {
    i := i + 1;
    while i != 0 { i := 0 }   // resets i every outer iteration
}
```

This diverges. But with the inner loop read as a no-op, the outer obligation became
`100 - (i + 1) < 100 - i`, which is a tautology — so the engine returned `Valid` and the
report claimed `Total` for a program that never halts. A termination proof for a divergent
program is precisely the claim this crate exists to make honestly, so this is the worst
class of defect in it: not a missing proof, but a wrong one.

The fix is to havoc exactly the variables the inner body can write, since after the inner
loop each holds the result of applying the body some unknown number of times. A measure
that mentions one of them then reduces to a fresh variable and cannot be discharged, which
is the honest answer — the caller must supply a measure the inner loop cannot disturb, or
one that accounts for it. A measure that mentions none of them survives untouched, so the
common nested shape (an inner scan over `j` under an outer counter `i`) still proves.
`writes` supplies the write set; when it is incomplete, the effect is unknown outright
rather than under-approximated.

Two tests pin this: `a_nested_loop_cannot_make_the_outer_variant_look_healthy` (the
divergent program above must be refuted) and
`a_nested_loop_that_leaves_the_measure_alone_still_proves` (the sound nested shape must
still verify). Reverting the fix fails the first and leaves the second passing, which is
the signature of a soundness fix rather than a tightened heuristic.

### When the engine says `Unknown`, hand the formula to a solver

`smtscript` prints the *same* formula the engine reasoned about as SMT-LIB2, with
variables declared and the goal negated, so `unsat` from any compliant solver is a
proof:

```rust
let vars = [sum, i, n, step];
let q = Query::new(&vars, report.contract.goal);
println!("{}", q.to_smtlib2_string());
```

```text
(set-logic QF_BV)
(declare-fun x0_4 () (_ BitVec 4))
...
(assert (not (bvor ... )))
(check-sat)
(get-model)
```

Independence matters for a safety argument: a proof reproduced by a *different*
tool from a textual artifact is stronger evidence than one produced by the same
code that generated the obligation. The exporter needs no `std` — it writes into
any `core::fmt::Write`, including a fixed buffer on bare metal.

## Memory: `read`, `store`, and the frame condition

Bit-vector logic cannot say "this array element is unchanged". `mem` adds the one
theory that matters most for safety-critical code, without touching the decision
procedure: a memory of `2^addr_width` cells, each cell an ordinary symbolic word.

```rust
use discharge::mem::{declare, Mem};

smt::with_fresh(|| {
    let mut buf = [var(8); 4];
    let n = declare(2, 8, &mut buf);          // 4 cells, 8 bits each
    let m = Mem::new(&buf[..n], 8);

    let addr = var(2);
    let val  = var(8);
    let at   = var(2);

    // The frame condition, proved for every address and value.
    assert_eq!(smt::prove(m.frame_lemma(addr, val, at)), Verdict::Valid);

    // A write, then a read back.
    let readback = m.store_wp(addr, val, smt::eq(m.read(addr), val));
    assert_eq!(smt::prove(readback), Verdict::Valid);
});
```

Run it: `cargo run --features std --example memory`.

Reading at a *concrete* address is a slice index. Reading at a *symbolic* address
is an ite chain, `ite(a == 0, m[0], ite(a == 1, m[1], ...))`. Because the address
has exactly `addr_width` bits, every value names exactly one cell: the encoding is
exact, with no default cell and no aliasing.

Writing is not mutation. `store(m, a, v)` is a *simultaneous* update of every
cell, `m'[k] = ite(a == k, v, m[k])`, produced by `Mem::store_binds`. That is the
same mechanism `wp` uses for assignment, which is why a memory write slots into
verification-condition generation with no new machinery — hand the bindings to
`Stmt::AssignMany` and the write becomes part of the program the engine reasons
about.

Two consequences are worth stating, because they are where people trip:

1. **The frame condition is a theorem, not a chore.** "A write to `a` leaves `b`
   alone" follows from `frame_lemma` rather than needing to be re-stated at every
   call site.
2. **Old values must be captured explicitly.** A postcondition is evaluated in the
   final state, and substitution rewrites every cell variable in it, so
   `m.read(i)` written directly in a postcondition means the *new* contents. To
   talk about the old contents you assign them to fresh variables first — the same
   discipline as SPARK's `m'Old`. `tests/mem.rs` verifies a swap this way.

### The memory limit, stated plainly

Bounds are *structural*: an address is `addr_width` bits, so it cannot name a cell
outside the memory. Out-of-range access is unrepresentable rather than proved
absent, which is a strong guarantee — but it means you must size the memory to the
largest address the real code can produce, and if that is not known, this is the
wrong tool.

A loop over addresses (`for k in 0..n { m[k] := 0 }`) *is* verifiable, because
its invariant needs a quantifier and bounded quantifiers can be expanded — see the
next section.

Cost: a symbolic read is `2^addr_width` ites and the BDD sees all of them, so
`MAX_CELLS` caps a memory at 64 cells (6 address bits).

The smallest memory is *two* cells, not one. A single cell is a power of two, so `new`
used to accept it — but then `addr_width()` is 0, and no `Var` can be zero bits wide, so
there was no address type with which to read or write it. `new` now refuses it, matching
`declare`, whose `addr_width` is already `1..=MAX_ADDR_WIDTH`. `a_single_cell_memory_is_refused`
pins it.

## The exported query must mean what the engine proved

The SMT-LIB export exists so an independent solver can reproduce a proof from a textual
artifact. That is only worth anything if the artifact says the same thing the engine said,
and twice it did not.

A boolean is a one-bit word here, so the printer has to coerce one to the other. The coercion
printed `(= w (_ bv0 1))` while its own comment said `w != 0` — the negation. A constant goal
came out inverted: `truth(false)` was written as `(assert false)`, which every solver reports
`unsat`, so an external checker would have called an impossible obligation *proved*. The
spelling of `!=` is `distinct`.

The operator choice was wrong too. `not`, `and`, `or` and `xor` exist in both readings, and
the printer always used the bit-vector one, so `not(x == y)` became `(bvnot (= x y))` —
ill-sorted, since `bvnot` wants a bit-vector and a comparison is a boolean. A solver rejects
that file, and a lenient one reads something else.

The first fix made the *node's own width* decide: at width 1 the boolean operator, above it the
bit-vector one. That is still wrong, because a one-bit connective's sort depends on **where it
sits**, not on how wide it is. As the goal, `x & y == 1` wants `and`; as an operand of `bvadd` it
wants `bvand`, and `Bool` is not `(_ BitVec 1)`. The width rule emitted `(bvule (_ bv1 1) (or …))`,
which z3 rejects as ill-sorted. The sort now decides: `Bool` prints comparisons natively and
one-bit connectives as `and`/`or`/`xor`/`not`; `Bits` prints comparisons as
`(ite <cmp> (_ bv1 1) (_ bv0 1))` and one-bit connectives as `bvand`/`bvor`/`bvxor`/`bvnot`.

`examples/z3diff.rs` is the harness that settles this rather than an argument. It generates random
predicates over 1-, 2-, 3-, 4-, 8- and 12-bit variables, with arithmetic, bitwise ops, shifts
(including over-shifts), `truncate` in both directions, and `ite`; asks the engine; exports the
same predicate; and asks z3. Measured with the current harness: 800 predicates — 0 parse errors,
0 disagreements, 25 refused, 0 undecided; 3000 predicates — 0 parse errors, 0 disagreements,
97 refused, 0 undecided.

The random sweep alone was not enough, and the way it fell short is the point. It compares only
sat/unsat, and a random predicate over free variables is essentially never a tautology, so a
well-sorted *semantic* printer bug is invisible to it: changing the exporter's `Op::Sub` to print
`bvadd` instead of `bvsub` left it at `mismatch=0`, even though `bvsub` appeared in 39 of the 800
exports and every one was decided. The operator was exercised on every run and never *checked*.
So the harness also carries a corpus of 42 *tautologies by construction* (`sub.self` is
`x - x == 0`, `mul.one` is `x * 1 == x`, `shl.nibble` is `0x0f << 4 == 0xf0`, and so on, one or
more per operator), each chosen so that at least one plausible mutation of the operator it names
breaks the identity. The export asserts `(not p)`, so z3 must answer `unsat`; a wrong operator
makes it `sat`. That is the dual of the random sweep and the only shape sensitive to a change that
preserves satisfiability. Measured: 42 identities, 0 mismatches. Teeth verified by mutating the
printer — `bvsub`→`bvadd`, `bvmul`→`bvadd`, `bvand`→`bvor`, `bvshl`→`bvlshr`, `bvxor`→`bvor`, and
widening `zero_extend`→`sign_extend` each make the harness exit 1 with the failing identity named.

"Refused" means the engine answered `Unknown` (typically a mixed-width term) and the exporter
declined to write a query for it, so there is nothing for z3 to contradict. "Undecided" is the
other way an `Unknown` can arise: the export *is* well formed, but the engine gave no verdict, so
z3 is never asked. It is counted separately rather than folded into the agreement count, because a
case z3 never saw is not a case z3 agreed with; it is 0 at both sizes. With the width-based
printing rule restored the same harness gets 21 of 800 rejected outright by z3 as ill-sorted. The
harness needs `z3-solver` installed; it is a development tool and the crate itself still has no
dependencies.

The harness also *fails* when it should. It exits 2 if the `z3` module is not importable, and
exits 1 on any disagreement or any file z3 refuses, printing the failing query. That matters
because the first version could not fail at all: it folded "the oracle is not installed" and "z3
rejected the file we printed" into the same `parse_err` tally and exited 0 either way, so a
broken exporter and a missing dependency produced the same green-looking line. A check that
cannot fail is not evidence.

The harness also has to be run against the *defect* to be worth anything: an oracle that passes
both with and without the fix proves nothing, and the classification has to be right. My first
version called `prove(p) == Unsat` a disagreement with z3's `sat`; it is not, since `prove`
answers `Unsat` when `p` is identically false, which is a tautology failure like any
counterexample. `Unknown` on our side is likewise never a disagreement — the engine is allowed to
be conservative, and z3 deciding is a stronger result, not a conflict.

This bug is worth the space because of how it hid. The engine was right the whole time — every
verdict it returned was correct. Only the *text* was wrong, so nothing in the crate's own tests
could see it, and the unit tests had been asserting the ill-sorted shape and passing. It took
handing the artifact to a different solver to notice that the artifact did not say what the
engine meant.

A third export bug sat in the same printer. `truncate` changes a width in either direction,
and the printer emitted `((_ extract w-1 0) x)` for both. That is only valid when the result is
no wider than the source; for a *widening* `truncate` it produced `((_ extract 15 0) x0_8)` —
extracting bit 15 from an 8-bit vector, which no solver accepts. Widening is `zero_extend`, and
the source width now decides which form is printed.

A fourth was not a printing bug at all, which is why it took longest to see. The engine
*refuses* a mixed-width operation — it returns `Unknown` and sets an internal flag — but the
term still exists, and the exporter printed its tree. So a query the engine had already
declined to decide was written out as `(bvadd x0_12 x1_8)`, which z3 rejects as ill-sorted.
The export is the artifact whose whole purpose is independent checking, and it was the one
thing that could not be checked: a reviewer would see a file that failed to load and read it
as a broken proof rather than a refused term.

The fix is that the export consults the same flag the engine does. `smt::is_ill_formed` is
public for exactly this reason, and a refused query writes a comment saying so and no
`(check-sat)` — there is no formula to hand to a solver, and pretending otherwise is worse
than saying nothing. `the_export_refuses_an_ill_formed_term_instead_of_printing_it` pins both
halves, and `a_well_formed_query_is_still_exported_in_full` is the control, so the refusal
cannot silently widen into refusing everything.

This is the general shape to watch for: a refusal that lives in the *engine* but not in the
*artifact*. The engine and the printer share a term representation, not a decision, so every
refusal has to be re-applied on the printing side, and only a test on the printed text can
show that it was.

## Substitution must not walk a shift amount

A shift node stores its amount in the same field every other binary node uses for a term id.
`subst` walked that field regardless, so substituting through `x << 3` recursed into whatever
term happened to have id 3. When that term contained the shift itself, the recursion never
bottomed out: `wp` on a two-line program blew the stack. When it did not, the walk still
touched an unrelated term, so a stale or oversized id there could flip the `stale` flag and
turn a provable goal into `Unknown`.

The differential test over the weakest-precondition transformer found it. It generates random
straight-line and branching programs, evaluates the generated `wp` at every one of the 256
inputs, and compares against running the same program concretely — exhaustive, and it does not
depend on the BDD engine at all. The fix skips the payload field for `Trunc` and the three
shifts, which the rebuild already carries across.

## A DSL's operator set is a claim too

The whole point of `sym` is that a specification reads like the expression it describes, so a
gap in it is not cosmetic. The literal-operator impls covered `x + 1u32`, `x * 2u32`,
`x & 0xffu32` and `x | 1u32` — but not `x - 1u32` or `x ^ 0xffu32`, which were compile errors.
Nothing about the four that worked tells you the other two are missing; a user has to discover
it by failing to compile, and a reader of the module cannot see the asymmetry at all.

Subtraction and XOR by a constant are as natural as addition and AND, so all six are now
provided, and `tests/sym.rs` pins each one against the `smt` primitive it is defined as. The
same file's teeth: it also asserts the six are *different* from one another, so a future edit
that wires every literal operator to `add` fails rather than passing six consistent
identities. (The DSL had no test file before this, which is how the gap survived.)

## Mixed-width operations are refused, not truncated

A bit-vector operation has no natural width when its operands disagree. The engine used to
take the *left* operand's width and truncate the right one silently. Fuzzing the predicate
layer found what that costs: `trunc2(b) + (a + 115)` was computed in two bits, so the
right-hand sum was masked to `y & 3`, the sum came out 2 instead of 142, and a predicate that
is false at `(a, b) = (27, 144)` read as `Valid`. That is a proof of a false statement, found
by a random predicate rather than by a test I would have written.

The crate has no widening operation, so the honest answer is to refuse the term. Every
binary operation — arithmetic, bitwise, comparison — and both branches of `ite` now check
that their operands agree in width. When they do not, the query returns `Unknown`, the same
way it does after an arena overflow or a stale handle. It never returns a wrong `Valid`.

This is a behavioural change, and a deliberate one: a term that used to be silently truncated
is now refused. The remedy at a call site is to write the intended width with `truncate`,
which makes the intent visible where the truncation happens rather than in the middle of an
arithmetic expression.

## Differential fuzzing: the shapes I did not think to test

The fixed harnesses check the cases I wrote down. A fuzzer checks the ones I did not: random
expression trees over two 8-bit variables, each proved symbolically and compared against
enumeration over all 65 536 inputs. `Valid` when enumeration finds a violation, a witness
that does not violate, or `Unsat` for a satisfiable equation are all failures. The seed is
fixed, so a failure is reproducible.

It found a bug in the *test*, not the engine. The oracle used Rust's `wrapping_shl`, which
masks the shift count by the width — `x << 8` on a `u8` is `x` — while this crate's
documented semantics is that a shift by at least the width yields zero. The engine was
right; the oracle was wrong. That is worth stating plainly: a differential test only says
what its oracle says, and the first oracle here was wrong.

The teeth are real. Making the BDD `Xor` arm behave like `And` makes the fuzzer report
`(!b) == b` as `Valid`, which it is not. That mutation was applied, observed, and reverted.

## The blasting is checked against Rust, not against itself

The differential harness compared whole predicates at eight bits. Above four bits `mul`
exhausts the BDD budget and `prove` returns `Unknown`, so the *blasting* of `mul` — the part
that decides proofs — had never been exercised by a passing test. Only its evaluation had.
A bug in that arm would be unsound, and nothing would have caught it.

Every operation is now checked at widths the BDD can finish, with Rust's own wrapping
arithmetic as the oracle: `add`, `sub`, `mul`, `and`, `or`, `xor`, all three shifts,
`ult`/`ule`/`eq`, and `truncate`. Each equation is routed through `prove`, so the blast arm
runs, and a deliberately wrong equation is asserted *not* to be proved, so an engine that
proved everything would fail.

Writing this found a hole in the test itself: the first version checked shifts through
`evaluate`, which exercises `eval_term` and not `blast`. A mutation to the BDD shift arm
passed. Routing through `prove` with a concrete constant catches it, and that is verified by
mutation rather than assumed.

## Staleness is caught once, in the arena

Stamping proof objects with an arena generation raised the obvious follow-up: what *else*
carries a term id? `Var`, `Pred`, `Mem`, `Query` — none of them stamped. Reusing one after a
reset did not fail cleanly. It overflowed the stack, exactly as the `with_fresh` comment had
always said it would:

```
use-after-free in the term arena ... typically shows up as unbounded recursion
rather than a clean panic
```

The comment was right, and had been right for several rounds while I read past it. It
described the *symptom* rather than the *invariant*, so it read like documentation of
intended behaviour instead of a bug report about a missing check.

Stamping each type would be whack-a-mole, and the next type would forget. Instead every term
id records the generation that created it, the term accessors note a mismatch, and the
traversals refuse to descend into a stale handle. One check covers every handle-carrying type
at once, and a query that touches a stale handle returns `Unknown`.

The subtlety that took two attempts: checking the *current* node is not enough. A constructor
can read a stale node and then build a *current* node that refers back to the stale id, so
the graph holds a cycle whose every node is current. Guarding the root is not guarding the
traversal — once any stale handle is touched, the whole walk stops.

## A proof object must not change meaning underneath you

The twelfth hole, and the most serious: a proof whose *meaning* silently changed. A
`Certificate` stores a `Pred`, which is a term **id**, and `with_fresh` resets the arena so
ids restart at 0. So a certificate from one scope named a *different formula* in the next:

```
scope A statement id : Pred(Term(2))
scope B predicate id : Pred(Term(2))     <- id recycled
same id?             : true
prove(cert.statement()) in scope B : Counterexample
cert.weaken_to(y < 200) -> true          <- a certificate for a falsehood
```

The engine knew `y < 200` was false, and the certificate claimed it was proved. The comment on
`with_fresh` had warned about exactly this — "use-after-free in the term arena" — but a warning
is not a check, and the failure was silent rather than a panic.

The arena now carries a `generation`, bumped by every reset, and `Certificate` and
`Implication` record it. Every rule re-checks it: `statement()` and `antecedent()` return
`None`, `weaken_to`/`and`/`apply`/`then` return `None`, and `Verified::from_certificate`
returns `None`. A stale proof object composes into nothing rather than into a falsehood.

A bare `Var` or `Pred` still carries no generation, so the "one `with_fresh` per proof" rule
still stands for those — the type cannot catch it. What the generation covers is the case that
outlives a scope *by construction*: the objects designed to be carried.

## A wrapper must not overclaim

The eleventh hole, and the one that undercut the crate's central promise: an overclaiming
abstraction. `Verified<T>` documented itself as evidence that "the associated contract was
proved", but it stored no contract, and `new(value, cert)` accepted *any* certificate. The
kernel test had been doing the wrong thing and passing:

```rust
let cert = Certificate::discharge(x.le_val(255)).unwrap(); // proves x <= 255
let v = Verified::new(42u32, cert);                        // value is 42u32
```

Nothing connected the two, and the type's name asserted a connection.

The wrapper now stores the statement, so the claim is checkable: `from_certificate` takes the
statement *from* the certificate (it cannot attest to anything else), `new` discharges the
statement itself and returns `None` if it is not a theorem, and `statement()` hands the claim
back.

Two honest boundaries, because this is exactly where a proof wrapper invites overclaiming.
First, the wrapper does not establish that `value` satisfies `statement` — the statement is
over symbolic variables and the value is concrete, so no constructor can check the link.
Second, and easier to miss: because the statement is a theorem it is equivalent to `true`, so
it carries no semantic content about the value. Its value is bookkeeping — which theorem was
discharged — and the type prevents mismatched bookkeeping, not an untrue claim.

## A truncated witness has to say so

The ninth hole, and the most consequential instance of the class: a *witness* presented as
complete while missing variables. A model is the evidence for a refutation, so a truncated one
is evidence with a hole in it.

`Cex` inlines `MAX_CEX` (16) assignments, and `model` stopped filling at the cap with no record
that it had. Worse, `value_of` returned `None` for a *dropped* variable exactly as it does for
one that was never mentioned, so an incomplete model was indistinguishable from a complete one.
The probe asks for a goal whose negation forces all twenty variables to be fixed:

```
assignments reported : 16
variables touched    : 20
is_complete()        : false
rendered             : v0:u1 = 1, … v15:u1 = 1 … 16/20 shown (TRUNCATED)
```

`Cex` now carries `total`, the number of variables the model touched, and `is_complete()`
reports whether every one of them is present. The `Display` impl marks a truncated model too,
because a witness printed as if whole is the failure mode the flag exists to prevent.

## A negative answer has to say what it swept

The eighth hole, and the sharpest instance of the recurring class: a limit that silently means
something weaker than it looks, in the one function whose whole job is to *catch* the symbolic
engine being wrong.

`find_counterexample_by_enumeration` took a `limit` and returned `Option<u64>`, so `None` meant
two different things: "swept the whole domain and found nothing" and "stopped early and found
nothing". A caller reading `None` as "no counterexample exists" was wrong for the second. The
probe made it concrete — the claim `clamp(x, 20, 200) <= 100` is false, and the first witness is
`x = 101`:

```
limit=100 (a prefix)  : None   <- reads as "no counterexample"
limit=256 (the domain): Some(101)
```

The function now takes the **domain**, not a search budget — the domain *is* the search — and
returns `Search`, which separates `Witness(u64)` from `NoWitness`. `NoWitness` is explicitly a
statement about the domain that was searched, and `domain_of_bits(8)` derives `256` from the
input width so the domain cannot drift from the symbolic width or be mistyped.

`exhaustive.rs` was checked and is not affected: its domain is the whole type, derived from the
type itself, and termination uses `checked_add` so it cannot wrap. `None` there unambiguously
means "swept everything". The difference was the `limit` parameter, which let a caller pass a
prefix.

### A `verify_` name must not hand back a value the caller can drop

The library is honest — `for_all_u8` returns `false` for a refuted property — but the *macro*
built on it was not. `verify_exhaustive!` expanded to `for_all_u8(...)` and returned the
boolean, so the natural way to write it, as a statement:

```rust
verify_exhaustive!(a: u8 => a < 128);   // false: 128..=255 violate it
println!("still here");
```

ran to completion and printed `still here`. Every sibling macro in the module (`verify!`,
`verify_implies!`, `contract!`, `proof!`) panics on a failed obligation, so the one macro whose
name also begins with `verify` was the one that could be ignored — and a reader who trusts the
name would not look for a returned boolean to check.

The fix makes it a statement: it finds the smallest violation and panics with it, naming the
witness (`counterexample a = 128`). Callers who want the boolean call `for_all_u8` directly. The
teeth are `exhaustive_macro_rejects_falsehoods`, a `#[should_panic]` test that pins both the
failure and the witness it reports.

The general question, and the third time this class has appeared: **which of a function's
results is a claim, and can the caller silently ignore it?** A returned `bool` is easy to drop; a
`panic` or a type is not. When a name promises verification, the failure has to be unmissable.

## An unreachable precondition is not a proof

The seventh hole, and the second of the vacuity kind. `verify(s, pre, post)` generates one
condition, `pre => wp(body, post)`. When `pre` is unsatisfiable that condition is a theorem
whatever the body and postcondition say — so every obligation discharges, `is_verified()`
returns true, and `establishes()` says `Total`, for a specification no run can ever reach:

```
pre satisfiable? : false
is_verified()    : true
establishes()    : Total
```

The body there was `x := 0` and the postcondition `x == 99`. The report called that `Total`.

This is the same failure as the bound hole seen from the other end: the first five holes let
a summary outrun its evidence, and these two give a proof with no evidence at all. Reachable
preconditions are a precondition *of* verification, not an assumption *about* it, and nothing
else in the tool was checking. The report now carries `Rule::VacuousPrecondition` as a
failure, so `establishes()` returns `Nothing`.

A note on where the check is needed. `verify_proc` uses a callee's `requires`, which is
normally reachable, and a `CallRequires` obligation still reports a real problem on an
unreachable path — so the gap is `verify` with a hand-written precondition, which is the case
the probe hit. The check is applied in `verify`, where every precondition arrives.

The teeth are two-sided: `an_unreachable_precondition_is_not_a_proof` pins the rejection, and
`a_reachable_precondition_is_still_proved` pins that a satisfiable precondition with a valid
contract still verifies, so the check cannot pass by rejecting everything.

### A call to a procedure that never returns is not a proof either

The third of the vacuity kind — reached through a `Call` rather than an
`Assume`. A callee whose postcondition is unsatisfiable never returns: `ensures false` says
there is no state in which the call completes. A `Call` is modelled as "assume `ensures`;
continue", so that assumption is `false`, the continuation becomes vacuous (`false => Q` is a
theorem), and every claim after the call discharges for free. With no loops in the program,
the report said:

```
is_verified() : true
establishes() : Total
```

for `boom(); x := 7` with postcondition `x == 7`, where `boom` is `requires true; ensures
false`. The program cannot get past the call, so the postcondition is never reached — and the
report called that progress.

This is the call-shaped twin of the unreachable-`Assume` hole, and it takes the same fix: the
walk records a `Rule::DivergentCall` finding at the call site, where the cut is, and reports
it as a failure. `Report::has_termination_proof` refuses it too, because a divergent call is a
termination finding and `correctness()` asks about termination on its own — otherwise
`loops == variants == 0` would read as progress on the strength of loops the program does not
have.

Two tests pin it, a matched pair again: `a_call_to_a_never_returning_proc_is_not_total` and,
as the control, `a_call_to_a_proc_that_merely_returns_nothing_is_still_total`. Reverting the
check fails the first and leaves the second green, so the fix refuses divergence, not calls.

The general shape, now seen three times: **a construct that cuts a path off makes everything
downstream vacuously true, and vacuous truth is indistinguishable from proof unless the cut is
recorded as a failure.** `Assume(false)`, an unsatisfiable precondition, and a never-returning
call are the three ways this fragment can cut a path, and each needed its own finding because
each is a different statement in the calculus.

## A bound must be wider than the address, or "all cells" is vacuous

The sixth hole, and the first of the *vacuity* kind. The previous five were summaries that
outran their evidence — a proof stronger than what was proved. This one is the dual: a proof
whose evidence is empty.

`Mem::check_addr_width` accepted a bound exactly as wide as the address, while its own
documentation told the caller to pass something wider. With a 4-cell memory the address is
2 bits, so a 2-bit bound cannot hold 4 — and "every cell is filled" is stated at
`bound == len`, i.e. `bound == 4`. The precondition was unsatisfiable, so the obligation was
vacuously true: `bound == 4 => P` *and* `bound == 4 => !P` both proved. A fill loop's
postcondition was "proved" without saying anything about the cells.

The tell was an impossible precondition reported as valid:

```
narrow(2-bit) bound == 4 satisfiable? : Valid
  pre_narrow => post_narrow          : Valid
  pre_narrow => NOT post_narrow      : Valid
```

The check now requires strictly more bits than the address, which is what every intended use
already passes — a loop counter must be wider than the address anyway, or `while k < len`
never terminates. `tests/mem.rs` pins the refusal, and also checks the *sensitivity* the old
behaviour lacked: at the intended width the property holds when the cells are zero and fails
when one is not.

## The memory family, positive side

The random memory family is 90% refutations, which tests strength but barely tests
soundness. A second family is therefore built the other way: templates that are *correct by
construction*, one per non-trivial rule (ite-chain read at a symbolic address, the frame
rule, `forall_below`, simultaneous bindings, read/write composition). Each must be proved by
the engine and must satisfy its own postcondition on every sampled array.

Each template also has a mutated twin — the same program with a false postcondition — which
must *not* be proved, so a template that verified for the wrong reason (a goal that collapsed
to `true`, say) cannot look like a success. 140 templates proved, 134 mutations refuted; the
six survivors are all the `n: 0` boundary, which is genuinely vacuous and is asserted to be
so explicitly rather than quietly skipped.

## The differential harness now covers memory

The harness in `tests/modular_differential.rs` compares the engine against concrete
execution, and until now it covered calls, loops containing calls, and obligation pressure.
The memory rules were the largest part of the crate with no such net, and they are the most
algebraic: an ite-chain read, a simultaneous binding list for a store, a frame lemma derived
by pushing one through the other, and a guarded quantifier for a prefix property. Each is a
place where the symbolic form could quietly disagree with an array.

The fourth family generates a program of stores — one of them at a *symbolic* address — plus
a postcondition, then checks both directions against an enumerated state space of four 8-bit
cells:

* `Valid` means no sampled `(initial array, address)` may violate the postcondition.
* anything else means some sampled input must violate it, and the search must find one.

The state space is small and closed, so unlike the call family this is an equivalence rather
than a one-way implication. Both directions are asserted, and the family fails if it is
vacuous in either — no case proved, or no case refuted. A companion test feeds a
deliberately wrong store rule (one that ignores the address and clobbers every cell) through
the same comparison to confirm the family can see a bad rule at all; with `store_binds`
actually broken, the family reports `VERIFIED but 4320 sampled (array, address) pairs
violate`.

## A guard compares an index, it does not truncate it

`quant::forall_guarded` and `quant::exists_guarded` quantify over a range while the upper
bound is a symbolic word — "every cell below the cursor". Their guard used to be built as
`ult(word(k, bits(bound)), bound)`, which truncates the concrete index `k` to the bound's
width. An index at or above `2^bits(bound)` then wrapped to a small value and satisfied the
guard, so an index provably *outside* the bound was treated as inside it. For
`exists_guarded` that is a soundness hole rather than a nuisance, because a satisfiable
guard weakens the disjunction: the formula becomes provable while the real obligation is
not. With `hi = 3` and a one-bit bound, `exists_guarded` came out `Valid` on an input whose
true form had a counterexample.

The guard now checks the index against the representable range first. An index that does
not fit is at least `2^bits(bound)`, hence provably `>= bound`, so the guard is `false` —
the truth rather than a wrap. The intended use, `Mem::forall_below` over a memory whose
cells match the bound's width, was never affected; the hole was reachable only through the
public `quant` API with a bound narrower than the range.

`tests/quant.rs` pins both directions: the guarded expansion must agree with the truth at a
narrow bound, and must be unchanged at a bound wide enough for every index.

## A derived frame says whether it is complete

The frame rule compares what a callee *claims* to write against what its body really
writes. That second set is derived from the syntax, and it is capped at `MAX_WRITES`.
Truncating it silently was a soundness hole that defeated the very check added to close
the first one: an under-complete "real" frame is exactly the condition the rule exists to
reject, so a callee writing more than `MAX_WRITES` variables looked like one writing
exactly `MAX_WRITES`, and a caller could prove that a clobbered variable survived.

So `writes` does not return `(array, count)` any more. It returns a `Frame`, whose
`complete()` is `false` when the body writes more than the cap, and every consumer treats
that as an unmodelled program rather than a partially modelled one:

```rust
let derived = wp::writes(callee.body);
if !derived.complete() { return false; }   // `Stmt::frame` refuses the call
```

`unchanged_vars` returns nothing for such a call and `unchanged` answers `false` — no
caller variable is known to survive a body the engine cannot fully see. A count that stops
at the cap is indistinguishable from a body that writes exactly that many, which is why a
flag had to be part of the type rather than a separate return value.

`MAX_WRITES <= MAX_CALL_ARGS` is now a compile-time assertion, because `unchanged_vars`
maps a complete frame into a buffer sized by `MAX_CALL_ARGS`; the two constants being
independent was a latent version of the same bug.

## The obligation cap fails loudly, never silently

`verify` collects side obligations — loop preservation, variants, exits, assertions, call
contracts — into a fixed-size buffer, `MAX_OBLIGATIONS`. It used to drop them silently once
the buffer was full. That is unsound in the worst possible way: a program with more than
sixteen side obligations could have a *failing* `LoopExit` land in the part that did not
fit, and the report would still say `verified` — and `Total`. The probe that found it
printed:

```
verified    : true
establishes : Total
--- ground truth: loop exits at i=10, so '100 <= i' is FALSE
```

A proof of a false statement is the one outcome a verifier must never produce. So the cap
now does two things:

* **Claim-carrying obligations report the drop.** A dropped loop rule or call rule raises
  `Rule::ObligationOverflow`, whose goal is `false`, so `verified` becomes false and the
  claim shrinks to what was actually checked. Assertions raise the same flag. They were
  once exempt, on the argument that the backward walk still conjoins a dropped `assert c`
  into the weakest precondition, so the contract obligation catches it. That is true of
  `verify`, but it left `wp::obligations`' `complete` flag lying -- it returned `true`
  while dropping obligations -- and a truncated obligation list is not a fully checked
  claim, so the report has to shrink here too. See
  `assertions_beyond_the_cap_are_reported_not_hidden` in `tests/wp.rs`.
* **The overflow notice itself cannot be dropped.** A `Report` carries one slot more than
  `MAX_OBLIGATIONS`, reserved for a report-level finding. Without that reservation the
  notice would be dropped by the same full buffer that caused it — which is exactly how
  the first attempt at this fix failed.

`tests/modular_differential.rs` has an obligation-pressure family that pads a program with
assertions until the count crosses the cap and demands that nothing ever verifies; with the
fix reverted it fails at padding 15.

The low-level `wp::obligations` had the same shape of hole one level down. It returned a
count that saturates at `MAX_OBLIGATIONS`, so a caller could not tell a complete set of
that size from a truncated prefix — two different facts behind one number, exactly the
defect `writes` was fixed for. It now returns a third value, `complete`, which is `true`
only when every side obligation is in the buffer. `verify` already turned the flag into a
failure; this makes the same information available to a caller inspecting obligations
directly. `a_complete_obligation_set_reports_itself_complete` and
`too_many_obligations_is_reported_not_swallowed` pin both directions, and
`assertions_beyond_the_cap_are_reported_not_hidden` pins the assertion case, which was the
one still returning `true` while dropping.

## Differential testing: a proof must not outrun reality

The two soundness holes in the call rule were found by accident — by writing a test
that asserted the wrong thing and noticing the engine agreed. That is not a method, so
`tests/modular_differential.rs` is the method: it generates programs containing calls,
verifies them with the engine, and **interprets them concretely**, then demands:

> if the engine reports the caller verified, no concrete execution in a bounded
> enumeration violates the postcondition.

That is the direction that matters, because soundness is the property that, if broken,
lets a verifier certify a bug. The other direction — every reported failure has a real
counterexample — is checked where it is cheap, but it cannot be complete, since a
failure may come from a bound the enumeration does not reach.

Three things make the harness trustworthy rather than decorative:

1. **`smt::evaluate` is validated first.** The concrete evaluator is the oracle, so
   `the_evaluator_agrees_with_the_engine_on_every_operator` pins it against the
   bit-level engine for every operator and every input pair. An oracle that disagreed
   would send you chasing bugs in the wrong place.
2. **The search space targets the known failure shapes.** The generator varies what the
   callee writes (directly or through a nested call), which caller variables the rename
   maps, and whether the declared frame is correct, generous, or a lie. It also *seeds*
   the result variable before the call — without that seeding, a missing havoc rule is
   invisible, because there is no pre-call value to be confused with the post-call one.

   The loop family does the same for the loop rules: it varies the callee's contract
   (exact or merely true), the frame, the invariant and the variant, and it includes
   bodies that never advance the counter. That last shape is what makes termination
   observable: a diverging loop claimed total is a contradiction the harness can see.
3. **The property has been observed to fail.** With the havoc rule disabled, the
   harness fails at a specific case and input; with the frame-completeness check
   disabled, two tests fail; with the termination check reduced to counting variants,
   the loop family fails at case 4. `the_property_has_teeth` makes the same point inside
   the suite, by running one case under a deliberately wrong semantics for calls and
   requiring all 256 inputs to be caught. A check never seen to fail is not evidence.

   Note what the loop defect teaches: a behavioural harness cannot see a *proof* defect
   directly. A non-decreasing variant still terminates, so comparing against execution
   is blind to it. It became visible only through the contradiction between a
   termination claim and a divergence. When a rule's failure mode is "proves the wrong
   thing" rather than "does the wrong thing", look for the contradiction it licenses.

## Bounded quantification: the invariant a loop over memory needs

A fill loop's invariant is "every cell below `k` is zero". That is a quantifier,
and a bit-vector decision procedure has none. But it is a *bounded* quantifier, and
a bounded quantifier is a finite conjunction, so it can simply be expanded:

```text
forall j < k { m[j] == 0 }   =>   (0 < k => m[0] == 0) && (1 < k => m[1] == 0) && ...
```

`Mem::forall_below` and `Mem::exists_below` do that expansion, which is what makes
a loop over addresses verifiable at all rather than needing a hand unroll:

```rust
// for k := 0; k < 4; k += 1 { m[k] := 0 }
let inv = m.forall_below(k, |cell| smt::eq_const(cell, 0));
let post = m.forall_cells(|cell| smt::eq_const(cell, 0));
```

Run it: `cargo run --features std --example memory`. The invariant verifies with
`Total` correctness; weakening it to "only `m[k]` is zero" makes the proof fail,
which is the control that shows the quantifier is doing real work rather than being
decorative. `tests/quant.rs` verifies a fill and a scan this way, and executes both
on real arrays.

Two details matter:

1. **The loop counter must be wider than the address.** With 4 addresses, a 2-bit
   counter cannot hold 4, so `while k < 4` would never exit. The counter is 3 bits
   and `Mem::addr_of` truncates it back to an address at the point of use — a new
   `truncate` primitive, since widths were previously immutable. Truncation wraps,
   so it is only sound once you have proved the index is in range; a wrapped write
   re-zeros an already-zero cell, which is why a fill survives it and a scan would
   not.
2. **A bound larger than the memory is fine, not a gap.** The quantifier ranges
   over the cells that exist, and those are the only addresses that can be named, so
   `forall k < 8` over four cells constrains exactly cells 0..3. My first version of
   this documentation claimed the opposite, and the test that caught it is
   `a_bound_larger_than_the_memory_is_not_a_problem`.

`quant` also offers the plain `forall_range`/`exists_range` over a slice, which is
useful outside the memory layer. The expansion is exact: a proof of the conjunction
is a proof of the quantified formula, and a counterexample names the index that
broke it.

### The bound has to be a number the tool can count to

`forall k < 1000` is a thousand copies of the predicate, so the cost is linear in
the range. Unbounded quantification over an unknown domain would need a different
decision procedure — that is the line between this crate and a real SMT solver, and
it is not a small one.

## Modular verification: procedures checked once, calls reasoned about through contracts

Without contracts, verifying a call means inlining the callee's body — exponential in
the call graph, and impossible for recursion. With them, a procedure is proved once
against its own contract and every call site costs two implications.

A `Proc` carries its body *and* its contract together, so it is impossible to assume
a postcondition nobody ever proved:

```rust
let sat_inc = Proc {
    name: "sat_inc",
    requires: smt::ule_const(x, 20),                                  // caller must establish
    ensures: smt::and(smt::ule_const(r, 20),                          // caller may assume
                      smt::implies(x.lt_val(20), smt::eq(r, x + 1u32))),
    body: &body,
};

assert!(wp::verify_proc(&sat_inc).is_verified());   // the "once" half

let call = Stmt::Call { proc_: &sat_inc, actuals: &[(x, a), (r, tmp)], writes: &[r] };
let report = wp::verify(&caller, smt::truth(true), post);   // the "many" half
```

`actuals` is a *simultaneous rename* of the callee's variables to the caller's, the
same mechanism assignment and memory writes use. `writes` is the callee's frame, and
`Stmt::frame` derives the check from it rather than trusting a hand-written list.

Run it: `cargo run --features std --example contracts`.

### Where a postcondition stops being bookkeeping

Put a call in a loop and the callee's postcondition becomes load-bearing. With
`sat_inc` above, the invariant `a <= 20 && k <= 4` is preserved *only* because the
contract promises `r <= 20`. Weaken the contract to the equation alone and the loop
stops being provable — `LoopPreserve` fails. The caller never reads the body, so that
bound is the entire reason the proof goes through. Both directions are tests
(`a_call_inside_a_loop_body_verifies` and its control
`dropping_the_bound_from_the_postcondition_breaks_the_loop`), because a positive test
alone would not show the postcondition was being used.

### What a call is not allowed to do

`Stmt::frame` rejects five things, and each is a real hole rather than tidiness. The
declared frame is checked against the frame **derived from the body** by `wp::writes`,
so it cannot be under-stated:

0. **`writes` must be complete.** This one is the sharpest. A caller that declares an
   empty frame for a callee that clobbers a variable is not making a bookkeeping
   error — it is asking the engine to prove that the variable survived, and the
   engine used to comply. I found this by probing rather than reasoning: the caller
   "proved" `s == 7` after a call that had overwritten `s` with `6`. A proof about a
   program that does not exist is worse than no proof, so the derived frame is now
   computed from the body (recursing through branches, loops and nested calls, and
   mapping a nested callee's writes through that call's actuals) and the declared
   frame must cover it. Over-declaring is still fine: the rule is conservative.
1. **A write the caller does not name.** The caller's state after the call would be
   unknown. Reported as `Rule::CallFrame`.
2. **A rename that is not a function** — a repeated callee variable.
3. **Two writes landing on one caller variable**, which is an order-dependent
   simultaneous assignment.
4. **A write landing on a variable the call also reads.** This one is not obvious.
   `ensures` is *assumed* after the call, so `x -> a, r -> a` would assume
   `a == a + a`, silently forcing `a == 0` on the caller and letting the engine prove
   anything about it. In-place update is not expressible by a rename; the caller must
   capture the old value into a temporary first, exactly as it must for a memory swap.
   I found this by writing a test that expected `frame` to accept the aliasing, and the
   engine had already been accepting it.

An unmodelled call is reported as an obligation that can never hold, not asserted
away, so a whole program can be checked in one run.

### A call havocs what it writes

The other half of the frame rule, and a soundness fix rather than a refinement. The
caller-side target of every write is renamed to a **fresh variable** in both the
assumed postcondition and the continuation. Without that the two sides share a name,
and the value the variable held *before* the call is mistaken for the value it holds
after — so `c := 99; c := bump(a); assert c == 99` verified. It no longer does. The
fresh name is universally quantified by the prover, which is exactly the right
reading: the caller must be correct for every result the contract permits.

### Two-state specifications need a snapshot, not an `old` operator

"The result equals the argument that came in, plus one" is a two-state property, and
it needs no new machinery. A variable the callee cannot write has the same value
before and after, so `old(x)` *is* `x` — provided the frame is honest, which is now
enforced. The snapshot is an ordinary assignment:

```rust
a := 5;  old_a := a;  c := bump(a)
assert c == old_a + 1 && a == old_a
```

What was missing was not a way to *write* `old(v)` but a way to **ask** which
variables survive, because the engine was already assuming it silently:

```rust
wp::unchanged(&bump, &actuals, a)    // true  -- read-only, so it survives
wp::unchanged(&bump, &actuals, c)    // false -- written, so its old value is gone
```

Both answer from the *derived* frame, so a caller cannot talk the query into a wrong
answer. For a written variable there is no query that helps: the caller must capture
the entry value into a temporary first, exactly as for a memory swap. That is a
discipline, not a convenience, and `the_snapshot_discipline_is_needed_for_written_variables`
is its control.

The havoc itself has a cap, and the cap has the same shape as the `writes` truncation it
shares a buffer size with: `havoc_writes` renames into a `MAX_CALL_ARGS` buffer and stops
at the end. That is sound only because `frame` refuses a declared frame with more than
`MAX_CALL_ARGS` distinct targets *before* the havoc runs, so a call that reaches the
rename can never overflow it. `a_declared_frame_longer_than_the_cap_is_refused` pins the
refusal, and its teeth are deliberate: it uses a body that writes a single variable, so
the derived-frame check passes and only the declared-frame cap can be what refuses the
call. (The first version of that test used a body at the `MAX_WRITES` cap and passed for
the wrong reason — check 0 refused it, not the cap — and did not fail when the cap was
removed. A test whose teeth are never pulled is a test that documents, not one that
guards.)

### The sharp edge, stated rather than hidden

`frame` checks the *shape* of the rename, not its meaning. A caller who wires the
result onto the wrong variable passes the check and gets a proof about a program it
did not write. And a caller that believes a contract whose body never established it
verifies anyway, because the caller does not read the body. Both are pinned by tests.
The discipline is therefore: verify every body against its contract with
`verify_proc`, and trust nothing else.

Recursion is not supported — a call graph with a cycle would need an induction
principle, and that is a different feature.

## What this is *not* — read this before trusting a green test

Honesty matters more than a nice README, so:

1. **Pointers, aliasing and concurrency are still out of scope.** `mem` models a
   bounded *array*, addressed by an integer. It does not model pointers, address
   arithmetic across objects, or two threads touching the same cell. You cannot
   state "this pointer is valid" or "these two threads do not race" in it.
   Quantifiers are bounded and expanded, so `forall` over an unknown domain is not
   available either — the range must be a number the tool can count to.
1b. **Termination needs a variant.** Without one, `wp` proves partial correctness
   only: a divergent loop can verify. There is no inference of variants — you
   supply the measure, the engine checks it decreases.
1c. **A nested loop's effect on an outer variant is handled by havocing, not by
   tracking.** `variant_after` treats an inner `while` as writing every variable its
   body can write, so a measure that mentions one of them becomes an obligation about a
   fresh variable and cannot be discharged. That is sound but conservative: you must
   supply an outer measure that does not depend on the inner loop's writes, or a measure
   that accounts for them explicitly. The alternative — reading the inner loop as a no-op —
   was a real soundness hole and is described under "Why `variant_after` must havoc a
   nested loop" below.
1d. **`with_fresh` must not be nested.** The inner call wipes the term arena and
   invalidates every `Var` the outer scope holds. One `with_fresh` per proof.
1e. **A call to a procedure whose postcondition is unsatisfiable is refused, not
   trusted.** `ensures false` means the callee never returns, so a caller's claims after
   the call are vacuous. The report carries a `Rule::DivergentCall` failure rather than
   calling it `Total`. This is the call-shaped twin of the unreachable-`Assume` and
   unreachable-precondition findings; see "A call to a procedure that never returns is not
   a proof either".
2. **There is a scaling wall, and the engine says so.** Boolean *equality of two
   wide multipliers* is the classic blow-up: `(a*b)*c == a*(b*c)` at 12 bits
   returns `Unknown`, and the test suite asserts exactly that. This is why
   `Unknown` is a first-class verdict: the engine refuses to guess. The wall is
   not removed, only pushed out.
3. **Two engines, one netlist.** BDDs are canonical and give equivalence
   checking for free, but they blow up on multipliers. When the BDD arena fills,
   the *same* bit-level circuit is handed to a CDCL SAT solver (`sat.rs`,
   `bitblast.rs`) that has no canonical-form wall. Both engines consume one
   netlist on purpose: two separate bit-slicers would drift, and an adder bug
   would then be caught in only one place.
   The SAT engine is exact but not fast, so it runs under a conflict budget and
   answers `Unknown` when it expires — a verifier that hangs is worse than one
   that declines. The gain is real but specific: `add_comm` at 64 bits is
   `Unknown` from the BDD engine alone and `Valid` with the fallback
   (`examples/probe.rs` prints the table). Multiplication equality stays out of
   reach at both engines' budgets; that is the honest state.
   The trade made here is still *no external process, no allocator,
   deterministic memory*. The SAT arena is a `static` in BSS, sized at compile
   time, and a capacity overrun yields `Unknown`, never a wrong verdict.
4. **`no_std` uses a single static arena**, so the symbolic engine is not
   re-entrant across interrupt contexts. Wrap queries in a critical section, or
   use one context per core. This is documented at the definition site.
5. **Counterexamples are witnesses, not optima.** A model is derived from a BDD
   path, so it is *a* violating input, not necessarily the smallest one.
   Enumeration finds the smallest.
6. **This is a research-grade experiment**, not a certified tool. It has no
   qualification evidence, no DO-178C tool qualification, and no independent
   review. Treat it as a demonstration of an idea, not as something to put on an
   aircraft without doing the certification work.

## Why BDDs at all

Because canonicity buys the properties that make "verification in the code"
practical:

- **Equivalence is node identity.** No proof search, no heuristics, no timeouts
  on the easy cases.
- **A proof is a small object.** A `Certificate` is a couple of machine words,
  so it can live in the artifact and be passed around, unlike a SAT proof trace.
- **No allocator.** A fixed arena gives a compile-time memory bound, which is
  what a safety case wants to see.

The variable order interleaves bit-planes by significance
(`level_of` in `smt.rs`), which keeps ripple-carry adders and unsigned
comparators linear in diagram size — the reason a 32-bit `x & 0xff < 256` proof
is instantaneous while a 12-bit multiplier equality is not.

## Layout

```
discharge/
├── src/
│   ├── lib.rs          crate root: module map, prelude, the three proof routes
│   ├── smt.rs          the decision procedure (the heart of the crate)
│   ├── bitblast.rs     bit-level circuit -> CNF, shared by both engines
│   ├── sat.rs          CDCL SAT solver: the fallback when the BDD arena fills
│   ├── sym.rs          symbolic DSL via operator overloading
│   ├── logic.rs        verified arithmetic + Q16.16 fixed point
│   ├── proof.rs        Curry–Howard kernel + certificates
│   ├── vc.rs           requires/ensures/invariant, Verified<T>
│   ├── contract.rs     runtime predicate checking
│   ├── exhaustive.rs   complete proofs by enumeration
│   ├── primitives.rs   total ops, Bounded<MIN,MAX>
│   ├── macros.rs       verify!, contract!, proof!, ...
│   ├── wp.rs           Hoare logic + automatic VC generation
│   │                   (also carries Proc + Stmt::Call for modular verification)
│   ├── smtscript.rs    SMT-LIB2 export for independent checking
│   ├── mem.rs          bounded symbolic memory + frame condition
│   └── quant.rs        bounded forall/exists, expanded to finite form
├── tests/
│   ├── smoke.rs        the engine proves real identities
│   ├── kernel.rs       the proof kernel, including a compile-fail case
│   ├── sym.rs          the DSL operators, each against the primitive it wraps
│   ├── differential.rs symbolic prover vs brute-force execution
│   ├── sat_engine.rs   the SAT solver vs brute force on raw CNFs
│   ├── wp.rs           generated conditions checked against execution
│   ├── mem.rs          memory proofs checked against real Rust arrays
│   ├── quant.rs        fill and scan loops, both verified and executed
│   ├── call.rs         modular verification, every positive with its control
│   ├── loopdiff.rs     verifier vs exhaustive execution, loops and claims included
│   └── modular_differential.rs  generated callers, verified then executed
├── examples/
│   ├── flight_control.rs  a realistic actuator path, all obligations discharged
│   ├── pipeline.rs        program -> conditions -> proofs -> SMT-LIB2
│   ├── memory.rs          read/store, the frame condition, and a fill loop
│   ├── contracts.rs       procedures verified once, calls reasoned about by contract
│   ├── report_probe.rs    a report's verdict must not depend on the arena it is read in
│   ├── z3diff.rs          differential harness: engine vs z3 on the exported text
│   │                      (needs z3-solver; a development tool, not a dependency)
│   ├── kanidiff.rs        differential harness: engine vs Kani on compiled Rust
│   │                      (needs `cargo kani`; a development tool, not a dependency)
│   ├── verusdiff.rs       differential harness: engine vs Verus on a spec fn
│   │                      (needs the Verus driver; a development tool, not a dependency)
│   └── support/           the IR the two engine harnesses share, so they check the
│                          same formulas rather than two drifting corpora
└── scripts/
    ├── gate.sh            every gate in one command, failing loudly
    └── test-count.sh      the exact passing-test count, only when all pass
```

## Building and testing

```console
# Everything, in one command that fails loudly on the first gate that does not hold
scripts/gate.sh

# Host, with the thread-local arena and the full test suite
cargo test --features std

# Bare metal: no std, no allocator, no dependencies
rustup target add thumbv7em-none-eabihf
cargo build --no-default-features --target thumbv7em-none-eabihf
```

`scripts/gate.sh` runs clippy (with `-D warnings`), the test suite, the bare-metal
`no_std` build, a zero-dependency check, and the z3 differential oracle. It exists because
the gates were previously five separate commands quoted in prose, which is how a gate
quietly stops being run. It also refuses to report success when the z3 oracle is not
installed: an oracle that did not run is not evidence about the exporter. Two further gates
run the Kani and Verus differential oracles when those tools are present and *skip them
loudly* when they are not, because both are large downloads (Kani: a pinned nightly plus
CBMC; Verus: a self-contained bundle with its own z3) that a normal local run should not pay
for; CI installs them and runs them as hard gates.

### Two more oracles, for the engine instead of the exporter

`z3diff` checks the *exporter*: it prints a query and asks z3 to agree about that text.
`examples/kanidiff.rs` and `examples/verusdiff.rs` check the *engine*. Each takes predicates
the engine proved, compiles them into real programs, and asks an independent verifier to
prove the same property of that program:

* `kanidiff` compiles each case into a Rust function and asks **Kani** (AWS's model checker,
  over CBMC) to verify it.
* `verusdiff` compiles each case into a Verus `spec fn` and asks **Verus** (Viper plus SMT,
  with bit-vector reasoning) to verify it.

Neither backend ever sees a symbolic term or an SMT-LIB string, and the two are built on
different foundations, so agreement is agreement between three independently built decision
procedures. A blasting bug now has to survive agreement with *both* of them, which is a much
narrower coincidence than surviving one.

The design detail that matters is that the predicate and the generated program are *not*
produced independently. They are interpretations of one shared IR tree (`WExpr`/`PExpr`, in
`examples/support/mod.rs`), so "the same property" is structural rather than hoped for; and
the two harnesses share that module, so they are checking the same formulas rather than two
corpora that drift apart. Generating predicate and program separately would compare unrelated
formulas and every disagreement would be noise.

The harnesses have been checked for teeth by mutation, which is the only way to know they ask
a real question. Dropping the `+1` from the `Sub` blast (`borrow = TRUE` → `FALSE`) makes the
engine reject three true identities (`sub_self`, `add_sub_cancel`, `sub_zero`); changing the
`Eq` blast from `and` to `or` over the per-bit equalities makes it prove false ones. Both
mutations are caught by both harnesses, the second as `MISMATCH rand_N` on the random sweep.
Each harness also carries a negative control — `a - b == b - a`, false by construction — and
fails if either side *proves* it, so a run where "everything agreed" because nothing was
really asked cannot pass.

Four divergences surfaced while building these, and all are worth stating because they are
where a plausible harness would have quietly lied:

1. **Arena sharing.** One engine arena for all cases exhausted the node budget after about a
   dozen queries, so later cases came back `Unknown` and the harness reported the engine as
   weak when the *harness* had run the arena dry. Each case now gets its own arena.
2. **Shift semantics.** The engine defines a shift by `k >= width` to be 0 (or the sign bit),
   the SMT-LIB rule, while Rust's `<<`/`>>` are an overflow error there. Emitting `x << k`
   would have compared a different function, so the generated programs spell the engine's rule
   out in `shl_eng`/`lshr_eng`/`ashr_eng`.
3. **The classification matrix.** The first version counted "engine refuted + backend proved"
   as agreement. A mutated engine then produced `mismatch=0` and was caught only by the
   curated corpus. Now only the engine's `Unknown` is "no claim"; every other engine verdict
   is a definite claim the backend must not contradict.
4. **Verus's arithmetic and its summary counts.** `#[verifier(bit_vector)]` rejects
   `wrapping_mul` when an operand is a literal, and a constant like `255u8 * 255u8` is a
   rustc const-eval overflow error that aborts the whole run, so the generated file routes
   arithmetic through spec helpers that wrap via `as u8`. And Verus's
   `verification results:: N verified, M errors` counts non-case items such as `main`, so the
   accounting check is on error *locations*, not on that sum.

Two corpus entries were also wrong — a bare `Not(And(..))` is not De Morgan, and
`guard <=> ite(guard,a,b)==a` fails at `a==b` — and the engine correctly refuted both. The
lesson that keeps recurring: when a harness disagrees, suspect the harness first, but *check*.

The engine's `Unknown` on `mul_comm` (an 8×8 multiplier) is the documented size wall, not a
disagreement: both backends prove the identity, so the engine is incomplete there, which the
harnesses count separately (`undecided_identity=1`) and do not fail on. A *refuted* identity
is a soundness failure and does fail the run. Note that the SAT fallback also tries this
identity and also declines it, which is the intended outcome: the fallback moves the wall, it
does not remove it, and an incomplete-but-honest answer is what keeps the differential
harness meaningful.

The `differential` test is the one that makes the approach trustworthy: for a
family of predicates it checks that the symbolic prover and brute-force
execution give the *same* answer, and that any symbolic counterexample really
does violate the property.

## Where this sits in the Rust ecosystem

The other verification tools for Rust are a different *kind* of thing, and the
difference is worth stating before the comparison table, because it decides what
`discharge` can and cannot be used for.

**The established tools verify Rust you already wrote, out of process.** Kani
(AWS) compiles to CBMC and model-checks; Verus and Creusot and Prusti translate
Rust (or its MIR) into a logic and hand it to an external SMT solver; `hax`
extracts Rust into F\*/Coq for other tools to consume; Flux adds refinement
types checked by a solver. All of them need a bespoke toolchain or a nightly
compiler, and all of them invoke a solver (usually Z3) as a separate binary.

**`discharge` is a prover that compiles into your artifact.** The decision
procedure is bit-blasting BDDs in the crate, the proof is a value, and there is
no external solver, no plugin, no nightly feature. That is a narrower and more
awkward design point — it buys you a proof that can run where Z3 cannot — and it
costs you scale, as the limits below say.

The honest split:

| | `discharge` | Kani / Verus / Creusot / Prusti | `contracts` crate |
|---|---|---|---|
| What is verified | a model of the program, as an AST you build | the Rust function itself (MIR/IR) | nothing — runtime `assert` |
| Needs external solver | no | yes (Z3 / CBMC) | no |
| Toolchain | stable, `no_std`, zero deps | nightly or bespoke driver | stable |
| Runs on the target | yes (compiled in) | no (host-side) | yes (but unchecked) |
| Scope | bit-vectors, booleans, bounded quantifiers | first-order + arithmetic + more | — |
| Maturity | a sketch | industrial | widely used |

Two things follow. First, `discharge` does not compete with Kani or Verus on
verifying real Rust; it does not read your MIR. It verifies programs written in
its own `Stmt` AST (see `wp::Stmt`) — except for `exhaustive`, which runs real
functions over small domains and is the one place a claim is about compiled
code. Second, the niche it does occupy — a checked contract that can be
discharged *on the target*, with no solver in the loop — is not one the big
tools aim at, and it is the same niche a `no_std` flight build actually needs.

They are not rivals here so much as a second opinion. The crate uses Kani and
Verus as *differential oracles* in its test suite (`examples/kanidiff.rs`,
`examples/verusdiff.rs`): the engine's verdict on a predicate is checked against
each tool's verdict on the equivalent compiled program, so the three decision
procedures have to agree. They are invoked as subprocesses and are never
dependencies — the shipped crate still has none — but "an independent verifier
agrees" is a much stronger claim than "the tests pass", and it is available
precisely because these tools exist.

### Rust is moving toward contracts

This is the part that makes the design timely rather than idiosyncratic. Rust is
adding contracts to the language itself: `#[contracts::requires(...)]` and
`#[contracts::ensures(...)]`, tracked in [rust-lang/rust#128044][track] (open,
`B-experimental`). The implementation landed in [PR #128045][pr], and its
description says the intrinsics for evaluating pre- and post-condition
predicates exist **"for third-party verifiers"**.

[track]: https://github.com/rust-lang/rust/issues/128044
[pr]: https://github.com/rust-lang/rust/pull/128045

So the language is growing the same contract vocabulary this crate has been
experimenting with, and it is deliberately leaving a door open for tools like
this one to sit on top. That cuts both ways, and both ways are worth naming: it
validates the direction, and it means a home-grown DSL will eventually be
competing with a blessed, in-tree syntax. The durable contribution here is the
*engine* — the embedded decision procedure and the proof kernel — not the
surface syntax, which is the layer most likely to be absorbed.

### Is it useful, and is it a big deal?

Useful, in a narrow band. For safety-critical or embedded Rust where you want
SPARK-style contracts and a machine-checked discharge with **no external
toolchain and no solver process** — an MCU, a flight build, a `no_std` target
where you cannot ship Z3 — this is a working sketch of how to get there, and it
is checked hard: differential testing of the exporter against Z3, differential
testing of the *engine* against both Kani and Verus, mutation testing of its own
guards, and a test suite that fails when a soundness guard is removed. The popular
`contracts` crate does runtime checking only; the gap between "assert at run
time" and "prove for all inputs" is exactly the gap this crate is about.

A big deal, no — not as a general-purpose verifier. That space belongs to
Kani and Verus, and this crate does not enter it. Its value is as a *reference
implementation* of the no-solver, no_std corner, and as evidence that the shape
works: a prover that is a library, a proof that is a value, a contract that
compiles into the artifact you ship.

## The SPARK comparison, stated plainly

| | SPARK/Ada + `gnatprove` | `discharge` |
|---|---|---|
| Contracts in source | `Pre`, `Post`, `Type_Invariant`, `Assert` | `requires`, `ensures`, `invariant`, `verify!` |
| Prover location | external tool in the toolchain | **inside the compiled artifact** |
| Logic | full first-order + linear arithmetic + arrays | bit-vectors and booleans |
| Memory model | pointer/aliasing analysis | none |
| Scaling | industrial, handles large systems | good on masks/bounds/shifts, weak on wide multipliers |
| Qualification | extensive certification evidence | none |

The interesting part is not that `discharge` beats `gnatprove` — it does not, and
cannot, on scope. The interesting part is the *shape*: a prover that is a
library, a proof that is a value, and a contract that compiles into the artifact
you ship. Rust can do that, and this crate is a working sketch of how.

## License

MIT OR Apache-2.0.
