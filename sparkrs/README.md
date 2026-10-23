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
| `wp` | Hoare logic: weakest preconditions, automatic VC generation, loop rules |
| `smtscript` | SMT-LIB2 export, so an external solver can check the same formula |
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
3. **Only partial correctness is claimed.** Hoare logic says "correct if it
   exits". There is no variant, so a divergent loop can still be verified — and
   `tests/wp.rs` contains a test that proves a divergent loop and demonstrates the
   divergence by execution, so the boundary is documented rather than hidden.

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

## What this is *not* — read this before trusting a green test

Honesty matters more than a nice README, so:

1. **It does not model memory, pointers, aliasing, or concurrency.** The logic is
   bit-vectors and booleans. You cannot state "this pointer is valid" or "these
   two threads do not race" in it. That is a different tool.
1b. **Hoare logic gives partial correctness only.** `wp` does not prove
   termination; there is no variant. A divergent loop can verify.
1c. **`with_fresh` must not be nested.** The inner call wipes the term arena and
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
│   └── smtscript.rs    SMT-LIB2 export for independent checking
├── tests/
│   ├── smoke.rs        the engine proves real identities
│   ├── kernel.rs       the proof kernel, including a compile-fail case
│   ├── differential.rs symbolic prover vs brute-force execution
│   └── wp.rs           generated conditions checked against execution
└── examples/
    ├── flight_control.rs  a realistic actuator path, all obligations discharged
    └── pipeline.rs        program -> conditions -> proofs -> SMT-LIB2
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
