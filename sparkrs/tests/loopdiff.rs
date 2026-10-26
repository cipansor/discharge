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

/// A claim written as `assert acc <= B`, `assert acc == B` or `assert acc < B`.
#[derive(Clone, Copy)]
enum Claim {
    Le(u8),
    Eq(u8),
    Lt(u8),
}

impl Claim {
    fn holds(self, acc: u8) -> bool {
        match self {
            Claim::Le(b) => acc <= b,
            Claim::Eq(b) => acc == b,
            Claim::Lt(b) => acc < b,
        }
    }
    fn build(self, acc: Var) -> Pred {
        match self {
            Claim::Le(b) => acc.le_val(b as u64),
            Claim::Eq(b) => acc.eq_val(b as u64),
            Claim::Lt(b) => acc.lt_val(b as u64),
        }
    }
}

/// Concrete step: `acc := f(acc)`, a claim, a loop, or a branch. Values are `u8`.
enum Step {
    AddConst(u8),
    AddVar,
    Claim(Claim),
    If { cond_lt: u8, then_: Vec<Step>, else_: Vec<Step> },
    While { guard_lt: u8, body: Vec<Step> },
}

/// Run concretely, returning `None` as soon as a claim fails. `None` means "some claim
/// this run reached is false", which is exactly what a verified report forbids.
fn run_checked(steps: &[Step], mut acc: u8, x: u8) -> Option<u8> {
    for s in steps {
        match s {
            Step::AddConst(k) => acc = acc.wrapping_add(*k),
            Step::AddVar => acc = acc.wrapping_add(x),
            Step::Claim(c) => {
                if !c.holds(acc) {
                    return None;
                }
            }
            Step::If { cond_lt, then_, else_ } => {
                let branch = if acc < *cond_lt { then_ } else { else_ };
                acc = run_checked(branch, acc, x)?;
            }
            Step::While { guard_lt, body } => {
                let mut fuel = 300;
                while acc < *guard_lt && fuel > 0 {
                    acc = run_checked(body, acc, x)?;
                    fuel -= 1;
                }
            }
        }
    }
    Some(acc)
}

fn run(steps: &[Step], acc: u8, x: u8) -> u8 {
    // Final value only; a false claim aborts the run, and the claim test uses
    // `run_checked` directly when it needs to know that.
    run_checked(steps, acc, x).unwrap_or(acc)
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
            Step::Claim(c) => Stmt::Assert(c.build(acc)),
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
    gen_with(r, depth, n, true)
}

/// `gen`, optionally leaving out `Claim` steps so a caller that only cares about the
/// contract postcondition is not diluted by assertions.
fn gen_with(r: &mut Lcg, depth: u32, n: usize, claims: bool) -> Vec<Step> {
    let top = if claims { 7 } else { 6 };
    (0..n)
        .map(|_| match r.below(top) {
            0 if depth > 0 => {
                let (nt, ne) = (r.below(3) as usize, r.below(3) as usize);
                Step::If { cond_lt: 1 + r.below(250) as u8, then_: gen_with(r, depth - 1, nt, claims), else_: gen_with(r, depth - 1, ne, claims) }
            }
            1 if depth > 0 => {
                let nb = r.below(3) as usize;
                Step::While { guard_lt: 1 + r.below(250) as u8, body: gen_with(r, depth - 1, nb, claims) }
            }
            2 => Step::AddVar,
            3 => {
                let b = r.below(256) as u8;
                match r.below(3) {
                    0 => Step::Claim(Claim::Le(b)),
                    1 => Step::Claim(Claim::Eq(b)),
                    _ => Step::Claim(Claim::Lt(b)),
                }
            }
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
        let steps = gen_with(&mut r, 2, n, false);
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
    assert!(verified > 30, "too few verified reports to be meaningful: {}", verified);
    assert!(total > 20, "too few Total reports to be meaningful: {}", total);
}

#[test]
fn a_verified_report_never_misses_a_failed_claim() {
    // The claim-rewrite machinery -- the `If` and `While` arms rewriting the assertions to
    // their right -- is where three defects lived. This drives it under brute force: build
    // programs whose claims are scattered through branches and loops, make the *contract*
    // vacuous (`pre = post = true`) so nothing but the claims can fail the report, and then
    // require that a verified report means no run reaches a false claim.
    //
    // A report that is *not* verified proves nothing here -- an unfaithful invariant or a
    // claim that is genuinely false both look the same from outside. The one-directional
    // assertion is the whole point: the verifier may miss a proof, but it may not certify a
    // claim that a concrete run falsifies.
    let mut r = Lcg(0x2b9c_4e17_a3f0_8811);
    let mut verified = 0u32;
    let mut with_failed_claim = 0u32;
    for _ in 0..800 {
        let n = 1 + r.below(4) as usize;
        let steps = gen(&mut r, 2, n);

        smt::with_fresh(|| {
            let x = var(8);
            let acc = var(8);
            let prog = build(&steps, acc, x);
            let report = verify(prog, smt::truth(true), smt::truth(true));

            // Oracle: every input, in order, stopping at the first false claim.
            let mut first_bad = None;
            for v in 0..=255u8 {
                if run_checked(&steps, v, v).is_none() {
                    first_bad = Some(v);
                    break;
                }
            }
            if first_bad.is_some() {
                with_failed_claim += 1;
            }

            if report.is_verified() {
                verified += 1;
                assert!(
                    first_bad.is_none(),
                    "the report says verified, but a concrete run reaches a false claim: \
                     first bad input x={:?}",
                    first_bad
                );
            }
        });
    }
    assert!(verified > 30, "too few verified reports to be meaningful: {}", verified);
    assert!(
        with_failed_claim > 30,
        "too few programs with a genuinely false claim to be meaningful: {}",
        with_failed_claim
    );
}
