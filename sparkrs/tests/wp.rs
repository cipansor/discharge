//! Verification-condition generation, checked against execution.
//!
//! Two things are tested here, and they are different claims:
//!
//! 1. the *symbolic* proof and a brute-force run of the same function agree, and
//! 2. the *rules* are attributed correctly, so a failure points at the right
//!    clause instead of just reporting `false`.

use sparkrs::prelude::*;
use sparkrs::smt::{self, var, Verdict};
use sparkrs::wp::{self, find_counterexample_by_enumeration, Rule, Stmt};

/// A clamp, the canonical safety-critical shape: `y := min(max(x, lo), hi)`.
/// Written with nested `if`s so the verifier has to consider both branches.
fn clamp_exec(x: u8, lo: u8, hi: u8) -> u8 {
    if x < lo {
        lo
    } else if x > hi {
        hi
    } else {
        x
    }
}

#[test]
fn clamp_meets_its_contract_and_execution_agrees() {
    smt::with_fresh(|| {
        let x = var(8);
        let y = var(8);
        let (lo, hi) = (20u64, 200u64);

        let then_lo = Stmt::Assign { var: y, expr: smt::word(lo, 8) };
        let then_x = Stmt::Assign { var: y, expr: x };
        let else_hi = Stmt::Assign { var: y, expr: smt::word(hi, 8) };
        let inner = Stmt::If {
            cond: smt::ult_const(x, hi + 1), // x <= hi
            then_: &then_x,
            else_: &else_hi,
        };
        let outer = Stmt::If {
            cond: smt::ult_const(x, lo), // x < lo
            then_: &then_lo,
            else_: &inner,
        };

        let post = smt::and(y.ge_val(lo), y.le_val(hi));
        let v = wp::verify_contract(&outer, smt::truth(true), post);
        assert!(v.is_proved(), "clamp should meet its contract, got {}", v);

        // Independent check: no 8-bit input may escape the range.
        let witness = find_counterexample_by_enumeration(
            256,
            |_| true,
            |v| clamp_exec(v as u8, lo as u8, hi as u8) as u64,
            |_x, out| out >= lo && out <= hi,
        );
        assert!(witness.is_none(), "execution found a witness: {:?}", witness);
    });
}

#[test]
fn a_too_tight_bound_is_refuted_and_execution_agrees() {
    smt::with_fresh(|| {
        let x = var(8);
        let y = var(8);

        let then_lo = Stmt::Assign { var: y, expr: smt::word(20, 8) };
        let then_x = Stmt::Assign { var: y, expr: x };
        let else_hi = Stmt::Assign { var: y, expr: smt::word(200, 8) };
        let inner = Stmt::If {
            cond: smt::ult_const(x, 201),
            then_: &then_x,
            else_: &else_hi,
        };
        let outer = Stmt::If {
            cond: smt::ult_const(x, 20),
            then_: &then_lo,
            else_: &inner,
        };

        // The clamp guarantees [20, 200]; claiming [0, 100] is too strong.
        let v = wp::verify_contract(&outer, smt::truth(true), y.le_val(100));
        assert!(!v.is_proved(), "this bound is too tight and must be refuted");

        // Execution must agree, and must produce a witness.
        let witness = find_counterexample_by_enumeration(
            256,
            |_| true,
            |v| clamp_exec(v as u8, 20, 200) as u64,
            |_x, out| out <= 100,
        );
        assert!(witness.is_some(), "execution should also find a violation");
    });
}

#[test]
fn an_accumulator_loop_verifies_with_attributed_rules() {
    smt::with_fresh(|| {
        // i := 0; while i < 10 { i := i + 1 }   post: i <= 10
        let i = var(8);
        let init = Stmt::Assign { var: i, expr: smt::word(0, 8) };
        let step = Stmt::Assign { var: i, expr: i + 1u32 };
        let loop_ = Stmt::While {
            cond: i.lt_val(10),
            invariant: i.le_val(10),
            body: &step,
        };
        let prog = Stmt::Seq { first: &init, second: &loop_ };

        // The invariant is established by the initialisation, which the backward
        // walk accounts for through `pre => wp(init, I)`.
        let report = verify_program(&prog, smt::truth(true), i.le_val(10));
        assert!(
            report.is_verified(),
            "the accumulator bound should hold: {:?}",
            report.first_failure()
        );

        // Both loop rules are present and attributed.
        let mut preserve = false;
        let mut exit = false;
        for ob in report.obligations.iter().flatten() {
            match ob.rule {
                Rule::LoopPreserve => preserve = true,
                Rule::LoopExit => exit = true,
                _ => {}
            }
        }
        assert!(preserve, "expected a preservation obligation");
        assert!(exit, "expected an exit obligation");
    });
}

#[test]
fn a_broken_invariant_is_caught_by_the_preservation_rule() {
    smt::with_fresh(|| {
        let i = var(8);
        // i := 0; while i < 10 { i := i + 2 } with invariant i <= 10.
        // From i == 10 the guard fails, but from i == 8 the body gives 10; from
        // i == 9 the body gives 11, which breaks i <= 10. So preservation fails.
        let init = Stmt::Assign { var: i, expr: smt::word(0, 8) };
        let step = Stmt::Assign { var: i, expr: i + 2u32 };
        let loop_ = Stmt::While {
            cond: i.lt_val(10),
            invariant: i.le_val(10),
            body: &step,
        };
        let prog = Stmt::Seq { first: &init, second: &loop_ };

        let report = verify_program(&prog, smt::truth(true), i.le_val(10));
        let (ob, _v) = report
            .first_failure()
            .expect("i + 2 can push i past 10 while the guard still holds");
        assert_eq!(ob.rule, Rule::LoopPreserve);
    });
}

#[test]
fn hoare_logic_does_not_prove_termination() {
    smt::with_fresh(|| {
        // i := 1; while i != 0 { i := i + 2 }   post: i <= 255
        //
        // In u8, adding 2 to an odd number keeps it odd, and 0 is even, so the
        // guard never fails and the loop never exits. The invariant is `true`,
        // which is trivially preserved, and `true && i == 0` implies `i <= 255`.
        // So every obligation is discharged even though the loop diverges.
        //
        // This is the honest caveat of Hoare logic: it establishes *partial*
        // correctness, i.e. correctness if the loop exits. Termination needs a
        // variant, which this calculus does not have.
        let i = var(8);
        let init = Stmt::Assign { var: i, expr: smt::word(1, 8) };
        let step = Stmt::Assign { var: i, expr: i + 2u32 };
        let loop_ = Stmt::While {
            cond: smt::not(smt::eq(i, smt::word(0, 8))),
            invariant: smt::truth(true),
            body: &step,
        };
        let prog = Stmt::Seq { first: &init, second: &loop_ };

        let report = verify_program(&prog, smt::truth(true), i.le_val(255));
        assert!(
            report.is_verified(),
            "partial correctness holds even though the loop diverges: {:?}",
            report.first_failure()
        );

        // And here is the divergence, demonstrated by execution: stepping by 2
        // from an odd start never reaches 0, so the guard never fails. The step
        // budget is what stops the run, not the condition.
        let mut i_exec: u8 = 1;
        let mut steps = 0u32;
        while i_exec != 0 && steps < 1000 {
            i_exec = i_exec.wrapping_add(2);
            steps += 1;
        }
        assert_eq!(steps, 1000, "the loop ran the budget out without exiting");
        assert_ne!(i_exec, 0, "and the guard was still true at the end");
    });
}

#[test]
fn assertions_inside_a_body_are_obligations() {
    smt::with_fresh(|| {
        let x = var(8);
        let y = var(8);
        // y := x + 1; assert x < y.   In u8 this fails exactly at x == 255.
        let assign = Stmt::Assign { var: y, expr: x + 1u32 };
        let assertion = Stmt::Assert(smt::ult(x, y));
        let prog = Stmt::Seq { first: &assign, second: &assertion };

        let report = verify_program(&prog, smt::truth(true), smt::truth(true));
        let (ob, _v) = report
            .first_failure()
            .expect("x < y fails at x == 255 in u8");
        assert_eq!(ob.rule, Rule::Assertion);

        // Excluding the wrap makes the same body verify.
        let report = verify_program(&prog, x.lt_val(255), smt::truth(true));
        assert!(report.is_verified(), "should hold below the wrap");
    });
}

#[test]
fn substitution_matches_real_assignment_on_every_input() {
    // The assignment rule is substitution, so check it against execution on every
    // 8-bit value. `y := x + 1` turns the predicate `y == x` into `x + 1 == x`,
    // which holds exactly when u8 addition wraps to the same value it started
    // from, i.e. never.
    //
    // One `with_fresh` for the whole sweep: nesting them would wipe the arena
    // while `xs` and `ys` were still live.
    smt::with_fresh(|| {
        let xs = var(8);
        let ys = var(8);
        let rewritten = smt::substitute(smt::eq(ys, xs), &[(ys, xs + 1u32)]);

        let mut x: u64 = 0;
        while x < 256 {
            // Pin both variables to the concrete pre-state and decide the
            // rewritten predicate there.
            let holds = smt::prove_implies(
                smt::and(smt::eq_const(xs, x), smt::eq_const(ys, x)),
                rewritten,
            )
            .is_proved();
            let exec_holds = (x as u8).wrapping_add(1) == x as u8;
            assert_eq!(holds, exec_holds, "mismatch at x = {}", x);
            x += 1;
        }
    });

    // Sanity: the engine's answer is not vacuously true. The *unrewritten*
    // predicate `y == x` does hold whenever the two are equal.
    smt::with_fresh(|| {
        let xs = var(8);
        let ys = var(8);
        let holds = smt::prove_implies(smt::eq_const(xs, 7), smt::eq(ys, xs));
        assert!(!holds.is_proved(), "y == x is not a theorem for free y");
        let holds = smt::prove_implies(
            smt::and(smt::eq_const(xs, 7), smt::eq_const(ys, 7)),
            smt::eq(ys, xs),
        );
        assert!(holds.is_proved(), "y == x holds when both are 7");
    });
}

#[test]
fn the_exported_query_negates_the_goal() {
    smt::with_fresh(|| {
        let x = var(8);
        let goal = x.le_val(255);
        assert_eq!(smt::prove(goal), Verdict::Valid);

        // The engine proves the goal; the exported query asserts its negation, so
        // a compliant solver would answer `unsat`.
        let vars = [x];
        let q = Query::new(&vars, goal);
        let text = q.to_smtlib2_string();
        assert!(
            text.contains("(assert (not (bvule x0_8 (_ bv255 8))))"),
            "{}",
            text
        );
    });
}
