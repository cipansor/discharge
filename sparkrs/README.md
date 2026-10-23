# sparkrs — formal verification that lives inside the Rust code

> An experiment: what if Rust could carry its own proof tooling the way
> SPARK/Ada carries `gnatprove`? Not a plugin, not an external solver, not a
> nightly feature — a **bit-blasting decision procedure compiled into your
> artifact**, next to a Curry–Howard proof kernel and a contract vocabulary.

`no_std`. Zero dependencies. Fixed-size, heap-free arena. `#![forbid(unsafe_op_in_unsafe_fn)]`.

```rust
use sparkrs::prelude::*;
use sparkrs::sym::*;

// ∀ x:u8. (x & 0x0f) < 16          — proved by the embedded SMT engine
let proved = sparkrs::smt::with_fresh(|| {
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
[honesty]   (a*b)*c == a*(b*c) at 12 bits  : unknown (node budget exhausted)

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
| 1 | **Symbolic** — BDD decision procedure | `smt::prove`, `sym::*::prove()` | no (BDD wall) | no — it returns `Unknown` |
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
use sparkrs::prelude::*;
use sparkrs::smt::{self, var};
use sparkrs::wp::{self, Stmt};

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
use sparkrs::mem::{declare, Mem};

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

`Stmt::frame` rejects four things, and each is a real hole rather than tidiness:

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
1c. **A nested loop's effect on an outer variant is not tracked.** `variant_after`
   treats an inner `while` as a no-op, so an outer measure must already account
   for the inner loop. This is the usual obligation when nesting loops, but it is
   a real gap rather than a solved problem.
1d. **`with_fresh` must not be nested.** The inner call wipes the term arena and
   invalidates every `Var` the outer scope holds. One `with_fresh` per proof.
2. **The BDD engine hits a wall, and says so.** Boolean *equality of two wide
   multipliers* is the classic blow-up: `(a*b)*c == a*(b*c)` at 12 bits returns
   `Unknown`, and the test suite asserts exactly that. This is why `Unknown` is a
   first-class verdict: the engine refuses to guess.
3. **It is not a CDCL SAT solver.** BDDs are canonical and give free
   equivalence checking, but a modern SAT/SMT solver will beat them on many
   industrial formulas. The trade made here is *no external process, no
   allocator, deterministic memory* in exchange for weaker scaling.
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
sparkrs/
├── src/
│   ├── smt.rs          the decision procedure (the heart of the crate)
│   ├── sym.rs          symbolic DSL via operator overloading
│   ├── logic.rs        verified arithmetic + Q16.16 fixed point
│   ├── proof.rs        Curry–Howard kernel + certificates
│   ├── vc.rs           requires/ensures/invariant, Verified<T>
│   ├── contract.rs     runtime predicate checking
│   ├── exhaustive.rs   complete proofs by enumeration
│   ├── primitives.rs   total ops, Bounded<MIN,MAX>
│   └── macros.rs       verify!, contract!, proof!, ...
│   ├── wp.rs           Hoare logic + automatic VC generation
│   ├── smtscript.rs    SMT-LIB2 export for independent checking
│   ├── mem.rs          bounded symbolic memory + frame condition
│   ├── quant.rs        bounded forall/exists, expanded to finite form
│   └── wp.rs           also: Proc + Stmt::Call for modular verification
├── tests/
│   ├── smoke.rs        the engine proves real identities
│   ├── kernel.rs       the proof kernel, including a compile-fail case
│   ├── differential.rs symbolic prover vs brute-force execution
│   ├── wp.rs           generated conditions checked against execution
│   ├── mem.rs          memory proofs checked against real Rust arrays
│   ├── quant.rs        fill and scan loops, both verified and executed
│   └── call.rs         modular verification, every positive with its control
└── examples/
    ├── flight_control.rs  a realistic actuator path, all obligations discharged
    ├── pipeline.rs        program -> conditions -> proofs -> SMT-LIB2
    ├── memory.rs          read/store, the frame condition, and a fill loop
    └── contracts.rs       procedures verified once, calls reasoned about by contract
```

## Building and testing

```console
# Host, with the thread-local arena and the full test suite
cargo test --features std

# Bare metal: no std, no allocator, no dependencies
rustup target add thumbv7em-none-eabihf
cargo build --no-default-features --target thumbv7em-none-eabihf
```

The `differential` test is the one that makes the approach trustworthy: for a
family of predicates it checks that the symbolic prover and brute-force
execution give the *same* answer, and that any symbolic counterexample really
does violate the property.

## The SPARK comparison, stated plainly

| | SPARK/Ada + `gnatprove` | `sparkrs` |
|---|---|---|
| Contracts in source | `Pre`, `Post`, `Type_Invariant`, `Assert` | `requires`, `ensures`, `invariant`, `verify!` |
| Prover location | external tool in the toolchain | **inside the compiled artifact** |
| Logic | full first-order + linear arithmetic + arrays | bit-vectors and booleans |
| Memory model | pointer/aliasing analysis | none |
| Scaling | industrial, handles large systems | good on masks/bounds/shifts, weak on wide multipliers |
| Qualification | extensive certification evidence | none |

The interesting part is not that `sparkrs` beats `gnatprove` — it does not, and
cannot, on scope. The interesting part is the *shape*: a prover that is a
library, a proof that is a value, and a contract that compiles into the artifact
you ship. Rust can do that, and this crate is a working sketch of how.

## License

MIT OR Apache-2.0.
