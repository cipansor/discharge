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
            // `10 - i` decreases by one each iteration, so the loop terminates.
            variant: Some(smt::sub(smt::word(10, 8), i)),
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
            variant: None,
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
            // No variant: this loop genuinely does not terminate, so there is
            // nothing to supply. See the termination tests below for the case
            // where a variant is given and the proof fails.
            variant: None,
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

#[test]
fn a_variant_proves_the_loop_terminates() {
    smt::with_fresh(|| {
        // i := 0; while i < 10 { i := i + 1 }, variant `10 - i`.
        //
        // `10 - i` is a natural number that drops by one each iteration, so the
        // loop cannot run forever. Supplying it upgrades the result from partial
        // to total correctness.
        let i = var(8);
        let init = Stmt::Assign { var: i, expr: smt::word(0, 8) };
        let step = Stmt::Assign { var: i, expr: i + 1u32 };
        let loop_ = Stmt::While {
            cond: i.lt_val(10),
            invariant: i.le_val(10),
            variant: Some(smt::sub(smt::word(10, 8), i)),
            body: &step,
        };
        let prog = Stmt::Seq { first: &init, second: &loop_ };

        let report = verify_program(&prog, smt::truth(true), i.le_val(10));
        assert!(report.is_verified(), "{:?}", report.first_failure());

        // The variant obligation is present and is the one that carries the
        // termination argument.
        let variant_obs: Vec<_> = report
            .obligations
            .iter()
            .flatten()
            .filter(|ob| ob.rule == Rule::LoopVariant)
            .collect();
        assert_eq!(variant_obs.len(), 1, "expected exactly one variant rule");
        assert_eq!(variant_obs[0].discharge(), Verdict::Valid);
    });
}

#[test]
fn a_variant_that_does_not_decrease_is_refuted() {
    smt::with_fresh(|| {
        // i := 0; while i < 10 { i := i } with variant `10 - i`.
        //
        // The body makes no progress, so the measure never decreases. The loop
        // hangs, and the variant obligation is what reports it.
        let i = var(8);
        let init = Stmt::Assign { var: i, expr: smt::word(0, 8) };
        let step = Stmt::Assign { var: i, expr: i }; // no progress
        let loop_ = Stmt::While {
            cond: i.lt_val(10),
            invariant: i.le_val(10),
            variant: Some(smt::sub(smt::word(10, 8), i)),
            body: &step,
        };
        let prog = Stmt::Seq { first: &init, second: &loop_ };

        let report = verify_program(&prog, smt::truth(true), i.le_val(10));
        let (ob, _v) = report
            .first_failure()
            .expect("a loop that makes no progress cannot terminate");
        assert_eq!(ob.rule, Rule::LoopVariant);
    });
}

#[test]
fn a_wrapping_variant_is_caught() {
    smt::with_fresh(|| {
        // i := 1; while i != 0 { i := i + 2 } with variant `i`.
        //
        // This is the divergent loop from `hoare_logic_does_not_prove_termination`
        // with a variant bolted on. The measure wraps: from i == 253 the body
        // gives 255, which is *larger*, so `V' < V` fails and the termination
        // claim is refuted. Bit-vector arithmetic is what makes this catchable —
        // in unbounded integers `i + 2 < i` would simply be false everywhere.
        let i = var(8);
        let init = Stmt::Assign { var: i, expr: smt::word(1, 8) };
        let step = Stmt::Assign { var: i, expr: i + 2u32 };
        let loop_ = Stmt::While {
            cond: smt::not(smt::eq(i, smt::word(0, 8))),
            invariant: smt::truth(true),
            variant: Some(i),
            body: &step,
        };
        let prog = Stmt::Seq { first: &init, second: &loop_ };

        let report = verify_program(&prog, smt::truth(true), i.le_val(255));
        let (ob, verdict) = report
            .first_failure()
            .expect("the measure wraps, so it is not a variant");
        assert_eq!(ob.rule, Rule::LoopVariant);

        // The witness is the state where the wrap makes the measure grow.
        if let Verdict::Counterexample(c) = verdict {
            println!("wrapping variant refuted at: {}", c);
        }
    });
}

#[test]
fn the_variant_is_evaluated_through_a_conditional_body() {
    smt::with_fresh(|| {
        // while i < 10 { if i < 5 { i := i + 2 } else { i := i + 1 } }
        //
        // The next-iteration value of `10 - i` is not a single expression here:
        // it depends on the branch. The engine derives it as
        // `ite(i < 5, 10 - (i + 2), 10 - (i + 1))`, so the user still writes the
        // measure once.
        let i = var(8);
        let then_ = Stmt::Assign { var: i, expr: i + 2u32 };
        let else_ = Stmt::Assign { var: i, expr: i + 1u32 };
        let body = Stmt::If {
            cond: i.lt_val(5),
            then_: &then_,
            else_: &else_,
        };
        let loop_ = Stmt::While {
            cond: i.lt_val(10),
            invariant: i.le_val(10),
            variant: Some(smt::sub(smt::word(10, 8), i)),
            body: &body,
        };

        let report = verify_program(&loop_, i.le_val(10), i.le_val(10));
        assert!(
            report.is_verified(),
            "both branches reduce the measure: {:?}",
            report.first_failure()
        );
    });
}

#[test]
fn variant_after_is_symbolic_evaluation_not_weakest_precondition() {
    smt::with_fresh(|| {
        // Direct check of the helper: it must build an expression, so a
        // conditional comes out as `ite` rather than a conjunction, and
        // sequential composition runs in execution order.
        let x = var(8);
        let y = var(8);

        // x := x + 1
        let inc = Stmt::Assign { var: x, expr: x + 1u32 };
        let after = wp::variant_after(&inc, x);
        // The value of `x` after the increment is `x + 1`; asking the engine
        // whether that is greater than the original for x < 255 confirms it.
        let v = smt::prove_implies(x.lt_val(255), smt::ult(x, after));
        assert!(v.is_proved(), "x + 1 > x below the wrap: {}", v);

        // y := x; x := y + 1   =>   value of x afterwards is x + 1, not y + 1.
        let copy = Stmt::Assign { var: y, expr: x };
        let bump = Stmt::Assign { var: x, expr: y + 1u32 };
        let seq = Stmt::Seq { first: &copy, second: &bump };
        let after_seq = wp::variant_after(&seq, x);
        let v = smt::prove_implies(x.lt_val(255), smt::eq(after_seq, x + 1u32));
        assert!(v.is_proved(), "composition order is wrong: {}", v);

        // The same through an if: the value is the ite of the two branches.
        let t = Stmt::Assign { var: x, expr: smt::word(3, 8) };
        let e = Stmt::Assign { var: x, expr: smt::word(7, 8) };
        let branch = Stmt::If {
            cond: x.lt_val(4),
            then_: &t,
            else_: &e,
        };
        let after_if = wp::variant_after(&branch, x);
        let v = smt::prove_implies(x.lt_val(4), smt::eq(after_if, smt::word(3, 8)));
        assert!(v.is_proved(), "then-branch value wrong: {}", v);
        let v = smt::prove_implies(smt::not(x.lt_val(4)), smt::eq(after_if, smt::word(7, 8)));
        assert!(v.is_proved(), "else-branch value wrong: {}", v);
    });
}

#[test]
fn the_report_says_whether_termination_was_proved() {
    // A loop with a variant establishes total correctness.
    let total = smt::with_fresh(|| {
        let i = var(8);
        let step = Stmt::Assign { var: i, expr: i + 1u32 };
        let loop_ = Stmt::While {
            cond: i.lt_val(10),
            invariant: i.le_val(10),
            variant: Some(smt::sub(smt::word(10, 8), i)),
            body: &step,
        };
        verify_program(&loop_, i.le_val(10), i.le_val(10))
    });
    assert!(total.is_verified());
    assert!(total.has_termination_proof());
    assert_eq!(total.correctness(), wp::Correctness::Total);

    // The same loop without a variant establishes only partial correctness.
    let partial = smt::with_fresh(|| {
        let i = var(8);
        let step = Stmt::Assign { var: i, expr: i + 1u32 };
        let loop_ = Stmt::While {
            cond: i.lt_val(10),
            invariant: i.le_val(10),
            variant: None,
            body: &step,
        };
        verify_program(&loop_, i.le_val(10), i.le_val(10))
    });
    assert!(partial.is_verified(), "still a valid partial-correctness proof");
    assert!(!partial.has_termination_proof());
    assert_eq!(partial.correctness(), wp::Correctness::Partial);
}

#[test]
fn one_unannotated_loop_makes_the_whole_report_partial() {
    smt::with_fresh(|| {
        // Two independent loops, only the first carrying a variant. The report
        // must not claim total correctness: the second loop could still diverge.
        let i = var(8);
        let j = var(8);
        // Each loop's invariant has to be established on entry, so both counters
        // start at zero.
        let init_i = Stmt::Assign { var: i, expr: smt::word(0, 8) };
        let init_j = Stmt::Assign { var: j, expr: smt::word(0, 8) };
        let step_i = Stmt::Assign { var: i, expr: i + 1u32 };
        let step_j = Stmt::Assign { var: j, expr: j + 1u32 };
        let first = Stmt::While {
            cond: i.lt_val(5),
            invariant: i.le_val(5),
            variant: Some(smt::sub(smt::word(5, 8), i)),
            body: &step_i,
        };
        // The second loop's invariant must be established on entry, and nothing
        // constrains `j` before it, so `true` is the only honest choice. Its
        // preservation obligation is then trivial — but it still counts as a
        // loop, which is what makes the report partial rather than total.
        let second = Stmt::While {
            cond: j.lt_val(5),
            invariant: smt::truth(true),
            variant: None,
            body: &step_j,
        };
        let prog = Stmt::Seq {
            first: &init_i,
            second: &Stmt::Seq {
                first: &init_j,
                second: &Stmt::Seq { first: &first, second: &second },
            },
        };

        let report = verify_program(&prog, smt::truth(true), smt::truth(true));
        assert!(report.is_verified(), "{:?}", report.first_failure());
        assert!(
            !report.has_termination_proof(),
            "the second loop has no variant, so termination is not proved"
        );
        assert_eq!(report.correctness(), wp::Correctness::Partial);
    });
}
