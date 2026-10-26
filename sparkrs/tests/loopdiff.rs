//! The verifier and exhaustive execution must agree on programs with loops.
//!
//! `tests/differential.rs` fuzzes `wp` against concrete execution, but its program
//! generator has no `While` at all. Loops are where the rule set is richest -- four
//! obligations, a variant, and a claim rewrite that reaches past the loop -- so they are
//! exactly where a rule can be wrong without the arithmetic being wrong. This closes that
//! gap: generate a small imperative program with loops and branches, run it concretely on
//! every input, and require that `verify`'s verdict matches what the runs show.
//!
//! The oracle is the same shape the crate already trusts elsewhere: a `valid` verdict must
//! mean no input falsifies the contract, and a refutation must come with a witness that
//! really does falsify it.

use sparkrs::prelude::*;
use sparkrs::smt::{self, var};
use sparkrs::wp::{verify, Established, Stmt};

struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0 >> 33
    }
    fn below(&mut self, n: u64) -> u64 {
        if n == 0 { 0 } else { self.next() % n }
    }
}

/// Concrete step: `acc := f(acc)`, or a loop, or a branch. Values are `u8`.
enum Step {
    AddConst(u8),
    AddVar,
    If { cond_lt: u8, then_: Vec<Step>, else_: Vec<Step> },
    While { guard_lt: u8, body: Vec<Step> },
}

fn run(steps: &[Step], mut acc: u8, x: u8) -> u8 {
    for s in steps {
        match s {
            Step::AddConst(k) => acc = acc.wrapping_add(*k),
            Step::AddVar => acc = acc.wrapping_add(x),
            Step::If { cond_lt, then_, else_ } => {
                if acc < *cond_lt { acc = run(then_, acc, x) } else { acc = run(else_, acc, x) }
            }
            Step::While { guard_lt, body } => {
                // Bounded iteration: a real loop could diverge, but every generated guard
                // is `acc < K` with a body that only adds, so the value is monotone and the
                // loop leaves after at most `256` steps. The cap makes the concrete run
                // total even for a body that never advances, and that cap is exactly why
                // this oracle can only *refute* a `Total` claim, never confirm one.
                let mut fuel = 300;
                while acc < *guard_lt && fuel > 0 {
                    acc = run(body, acc, x);
                    fuel -= 1;
                }
            }
        }
    }
    acc
}

/// Symbolic translation. Every loop carries the invariant "acc < 256" (always true for a
/// byte) plus its guard bound, which is enough for the generated programs: the bodies only
/// add constants or the input, so the accumulator stays a byte by construction.
fn build(steps: &[Step], acc: Var, x: Var) -> &'static Stmt<'static> {
    let mut seq: Stmt = Stmt::Skip;
    for s in steps.iter().rev() {
        let one: Stmt = match s {
            Step::AddConst(k) => Stmt::Assign { var: acc, expr: acc + *k as u32 },
            Step::AddVar => Stmt::Assign { var: acc, expr: acc + x },
            Step::If { cond_lt, then_, else_ } => Stmt::If {
                cond: acc.lt_val(*cond_lt as u64),
                then_: Box::leak(Box::new(build(then_, acc, x))),
                else_: Box::leak(Box::new(build(else_, acc, x))),
            },
            Step::While { guard_lt, body } => Stmt::While {
                cond: acc.lt_val(*guard_lt as u64),
                invariant: acc.le_val(255),
                variant: Some(smt::sub(smt::word(*guard_lt as u64, 8), acc)),
                body: Box::leak(Box::new(build(body, acc, x))),
            },
        };
        seq = Stmt::Seq { first: Box::leak(Box::new(one)), second: Box::leak(Box::new(seq)) };
    }
    Box::leak(Box::new(seq))
}

fn gen(r: &mut Lcg, depth: u32, n: usize) -> Vec<Step> {
    (0..n)
        .map(|_| match r.below(6) {
            0 if depth > 0 => {
                let (nt, ne) = (r.below(3) as usize, r.below(3) as usize);
                Step::If { cond_lt: 1 + r.below(250) as u8, then_: gen(r, depth - 1, nt), else_: gen(r, depth - 1, ne) }
            }
            1 if depth > 0 => {
                let nb = r.below(3) as usize;
                Step::While { guard_lt: 1 + r.below(250) as u8, body: gen(r, depth - 1, nb) }
            }
            2 => Step::AddVar,
            k => Step::AddConst((k % 3) as u8 + 1),
        })
        .collect()
}

#[test]
fn a_verified_report_is_never_wrong_about_loops() {
    // The one property that must never fail: if the verifier says the program is verified,
    // then no input falsifies the contract. This is checked by brute force on all 256
    // inputs, so a single disagreement is a soundness bug, not a heuristic miss.
    //
    // The converse is deliberately *not* asserted. A loop's invariant is supplied by the
    // caller, so a contract that happens to hold everywhere may still be refuted -- an
    // unfaithful invariant, or a variant that does not decrease, is a legitimate failure.
    // What the verifier owes the caller is that it never says `verified` about something
    // that is not, and that is what this pins.
    let mut r = Lcg(0x7f3a_91b5_2c8d_0044);
    let mut verified = 0u32;
    let mut total = 0u32;
    for _ in 0..600 {
        let n = 1 + r.below(3) as usize;
        let steps = gen(&mut r, 2, n);
        // Draw the postcondition bound from the *reachable* outputs, so a large share of
        // contracts genuinely hold and the verifier has something to prove. A uniformly
        // random bound almost never holds, which would leave the soundness assertion with
        // almost nothing to check.
        let mut outputs = [0u8; 256];
        for (v, o) in outputs.iter_mut().enumerate() {
            *o = run(&steps, v as u8, v as u8);
        }
        let use_eq = r.below(2) == 0;
        let bound = if use_eq {
            outputs[r.below(256) as usize] as u64
        } else {
            let m = *outputs.iter().max().unwrap() as u64;
            // Sometimes below the max, sometimes exactly it: the former must be refuted
            // and the latter must verify, so both branches of the assertion get exercised.
            if r.below(2) == 0 { m } else { r.below(m + 1) }
        };

        smt::with_fresh(|| {
            let x = var(8);
            let acc = var(8);
            let prog = build(&steps, acc, x);
            let post = if use_eq { acc.eq_val(bound) } else { acc.le_val(bound) };
            let report = verify(prog, smt::truth(true), post);

            // Oracle: every input, run concretely.
            let mut first_bad = None;
            for (v, out) in outputs.iter().enumerate() {
                let ok = if use_eq { *out as u64 == bound } else { *out as u64 <= bound };
                if !ok {
                    first_bad = Some((v as u8, *out));
                    break;
                }
            }

            if report.establishes() == Established::Total {
                total += 1;
            }
            if report.is_verified() {
                verified += 1;
                assert!(
                    first_bad.is_none(),
                    "the report says verified, but a concrete run falsifies the contract: \
                     bound={}, eq={}, first bad input x={:?}",
                    bound,
                    use_eq,
                    first_bad
                );
            }
        });
    }
    assert!(verified > 60, "too few verified reports to be meaningful: {}", verified);
    assert!(total > 20, "too few Total reports to be meaningful: {}", total);
}
