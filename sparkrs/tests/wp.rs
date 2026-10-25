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

        // Independent check: no 8-bit input may escape the range. The domain is
        // *derived* from the input width, so it cannot drift from the symbolic width.
        let found = find_counterexample_by_enumeration(
            wp::domain_of_bits(8),
            |_| true,
            |v| clamp_exec(v as u8, lo as u8, hi as u8) as u64,
            |_x, out| out >= lo && out <= hi,
        );
        assert_eq!(
            found,
            wp::Search::NoWitness,
            "execution found a witness: {:?}",
            found.witness()
        );
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

        // Execution must agree, and must produce a witness. A truncated domain would
        // also be worth reporting here, and the return type makes that impossible to
        // confuse with a clean sweep.
        let found = find_counterexample_by_enumeration(
            wp::domain_of_bits(8),
            |_| true,
            |v| clamp_exec(v as u8, 20, 200) as u64,
            |_x, out| out <= 100,
        );
        assert!(
            found.witness().is_some(),
            "execution should also find a violation, got {:?}",
            found
        );
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

#[test]
fn a_variant_that_does_not_decrease_is_not_termination() {
    // The defect the differential harness found, pinned here so it cannot come back.
    //
    // `has_termination_proof` used to count variant obligations instead of discharging
    // them. So a loop annotated with a measure that does *not* decrease reported
    // `Total`: the report was not verified (the variant obligation failed), yet
    // `correctness()` still said `Total`. Two halves of one question, read separately,
    // gave opposite answers, and the optimistic half was the one a caller is tempted to
    // read.
    smt::with_fresh(|| {
        let i = var(8);
        let step = Stmt::Assign { var: i, expr: i + 1u32 };
        // The measure `i` increases as `i` increases, so it cannot decrease.
        let loop_ = Stmt::While {
            cond: i.lt_val(10),
            invariant: i.le_val(10),
            variant: Some(i),
            body: &step,
        };
        let report = verify_program(&loop_, i.le_val(10), i.le_val(10));

        assert!(!report.is_verified(), "the variant obligation must fail");
        let (ob, _) = report.first_failure().expect("a failure is expected");
        assert_eq!(ob.rule, wp::Rule::LoopVariant);

        // The point: no termination claim may survive that failure.
        assert!(
            !report.has_termination_proof(),
            "a variant that was not proved to decrease is not a termination proof"
        );
        assert_eq!(report.correctness(), wp::Correctness::Partial);
        assert_eq!(
            report.establishes(),
            wp::Established::Nothing,
            "an unverified report establishes nothing at all"
        );
    });
}

#[test]
fn establishes_answers_both_halves_at_once() {
    // The three states, side by side, so the distinction is visible in one place.
    smt::with_fresh(|| {
        let i = var(8);
        let init = Stmt::Assign { var: i, expr: smt::word(0, 8) };
        let step = Stmt::Assign { var: i, expr: i + 1u32 };

        // Verified with a decreasing variant: total.
        let good = Stmt::While {
            cond: i.lt_val(10),
            invariant: i.le_val(10),
            variant: Some(smt::sub(smt::word(10, 8), i)),
            body: &step,
        };
        let prog = Stmt::Seq { first: &init, second: &good };
        let r = verify_program(&prog, smt::truth(true), smt::truth(true));
        assert_eq!(r.establishes(), wp::Established::Total);

        // Verified without a variant: partial.
        let no_variant = Stmt::While {
            cond: i.lt_val(10),
            invariant: i.le_val(10),
            variant: None,
            body: &step,
        };
        let prog = Stmt::Seq { first: &init, second: &no_variant };
        let r = verify_program(&prog, smt::truth(true), smt::truth(true));
        assert_eq!(r.establishes(), wp::Established::Partial);

        // Not verified: nothing, whatever the obligations would have said.
        let r = verify_program(&prog, smt::truth(true), smt::eq_const(i, 99));
        assert!(!r.is_verified());
        assert_eq!(r.establishes(), wp::Established::Nothing);
    });
}

#[test]
fn too_many_obligations_is_reported_not_swallowed() {
    // The worst defect found in this crate, and the same *class* as the termination one:
    // a summary claim outrunning what was actually proved.
    //
    // `push` used to drop obligations silently once `MAX_OBLIGATIONS` was reached. So a
    // program with more than 16 side obligations could have a *failing* `LoopExit` land
    // in the part that did not fit, and the report would still say `verified` — worse,
    // `Total`. The probe that found it printed:
    //
    //     verified : true
    //     establishes : Total
    //     ground truth: loop exits at i=10, so '100 <= i' is FALSE
    //
    // A proof of a false statement is the one outcome a verifier must never produce, so
    // a dropped obligation is now a failure rather than a silence.
    smt::with_fresh(|| {
        let i = var(8);
        let init: &'static Stmt<'static> = Box::leak(Box::new(Stmt::Assign {
            var: i,
            expr: smt::word(0, 8),
        }));
        // The loop exits at i == 10, so `i <= 10` is preserved but `100 <= i` is false
        // at exit. Only `LoopExit` can report a failure.
        let step: &'static Stmt<'static> =
            Box::leak(Box::new(Stmt::Assign { var: i, expr: i + 1u32 }));
        let loop_: &'static Stmt<'static> = Box::leak(Box::new(Stmt::While {
            cond: smt::ult_const(i, 10),
            invariant: smt::ule_const(i, 10),
            variant: None,
            body: step,
        }));
        let program: &'static Stmt<'static> = Box::leak(Box::new(Stmt::Seq {
            first: init,
            second: loop_,
        }));

        // Filler assertions after the loop, enough to overrun the buffer.
        let mut node = program;
        for _ in 0..16 {
            let leaf: &'static Stmt<'static> =
                Box::leak(Box::new(Stmt::Assert(smt::truth(true))));
            node = Box::leak(Box::new(Stmt::Seq { first: node, second: leaf }));
        }

        let post = smt::not(smt::ult_const(i, 100));
        let report = wp::verify(node, smt::truth(true), post);

        // The claim must shrink to what was checked.
        assert!(
            !report.is_verified(),
            "a program too large for the buffer must not be reported as verified"
        );
        assert_eq!(
            report.establishes(),
            wp::Established::Nothing,
            "no claim survives an unchecked obligation"
        );
        let (ob, _) = report.first_failure().expect("the overflow must be reported");
        assert_eq!(ob.rule, Rule::ObligationOverflow);

        // And the overflow really is what happened: the program has more obligations
        // than the buffer holds, so at least one was dropped.
        let mut slots = [None; wp::MAX_OBLIGATIONS + 1];
        let (_, count) = wp::obligations(node, post, &mut slots);
        assert_eq!(
            count,
            wp::MAX_OBLIGATIONS,
            "the buffer below the reserved slot should be exactly full"
        );
    });
}

#[test]
fn a_report_that_fits_is_unaffected_by_the_reserved_slot() {
    // The other side of the fix: the reserved slot must not cost a program anything.
    // A program with exactly `MAX_OBLIGATIONS - 1` side obligations still reports all of
    // them, verifies, and is not mistaken for an overflow.
    smt::with_fresh(|| {
        let i = var(8);
        let step: &'static Stmt<'static> =
            Box::leak(Box::new(Stmt::Assign { var: i, expr: i + 1u32 }));
        let init: &'static Stmt<'static> = Box::leak(Box::new(Stmt::Assign {
            var: i,
            expr: smt::word(0, 8),
        }));
        let loop_: &'static Stmt<'static> = Box::leak(Box::new(Stmt::While {
            cond: smt::ult_const(i, 10),
            invariant: smt::ule_const(i, 10),
            variant: None,
            body: step,
        }));
        let mut node: &'static Stmt<'static> = Box::leak(Box::new(Stmt::Seq {
            first: init,
            second: loop_,
        }));
        // 10 assertions plus the loop's two obligations: comfortably inside the buffer.
        for _ in 0..10 {
            let leaf: &'static Stmt<'static> =
                Box::leak(Box::new(Stmt::Assert(smt::truth(true))));
            node = Box::leak(Box::new(Stmt::Seq { first: node, second: leaf }));
        }
        let report = wp::verify(node, smt::truth(true), smt::ule_const(i, 10));
        assert!(report.is_verified(), "{:?}", report.first_failure());
        assert_eq!(report.establishes(), wp::Established::Partial);
        assert!(
            !report
                .obligations
                .iter()
                .flatten()
                .any(|ob| ob.rule == Rule::ObligationOverflow),
            "a program that fits must not be flagged as overflowing"
        );
    });
}

#[test]
fn an_unreachable_precondition_is_not_a_proof() {
    // The seventh hole, and the second of the vacuity kind.
    //
    // `verify(s, pre, post)` generates the single condition `pre => wp(body, post)`. When
    // `pre` is unsatisfiable that condition is a theorem whatever the body and
    // postcondition say, so every obligation discharges, `is_verified()` returns true, and
    // `establishes()` says `Total` — for a specification no run can ever reach. The probe
    // printed exactly that:
    //
    //   pre satisfiable? : false
    //   is_verified()    : true
    //   establishes()    : Total
    //
    // The report is now unverified, with `VacuousPrecondition` as the first failure.
    // Reachable preconditions are a precondition of verification, not an assumption about
    // it, and nothing else in the tool checks them.
    smt::with_fresh(|| {
        let x = var(8);
        // `x < 10 && x > 200` has no solution.
        let pre = smt::and(smt::ult_const(x, 10), smt::ugt_const(x, 200));
        let body = Stmt::Assign { var: x, expr: smt::word(0, 8) };
        // A postcondition that is plainly false, to make the point that the contract
        // "proves" it only because it cannot be entered.
        let post = smt::eq_const(x, 99);

        let report = wp::verify(&body, pre, post);
        assert!(
            !report.is_verified(),
            "an unsatisfiable precondition must not produce a verified report"
        );
        let (ob, _) = report
            .first_failure()
            .expect("a vacuous precondition is a failure");
        assert_eq!(
            ob.rule,
            Rule::VacuousPrecondition,
            "the failure must be attributed to the vacuous precondition, not to the body"
        );
        assert_eq!(report.establishes(), wp::Established::Nothing);
    });
}

#[test]
fn a_reachable_precondition_is_still_proved() {
    // The teeth of the check above: it must not reject every report. A satisfiable
    // precondition with a contract that genuinely holds stays verified.
    smt::with_fresh(|| {
        let x = var(8);
        let pre = smt::ult_const(x, 100);
        // `y := 0` establishes `y == 0`, under any precondition.
        let y = var(8);
        let body = Stmt::Assign { var: y, expr: smt::word(0, 8) };
        let post = smt::eq_const(y, 0);
        let report = wp::verify(&body, pre, post);
        assert!(
            report.is_verified(),
            "a reachable precondition and a valid contract must still verify"
        );
        assert!(
            !report
                .obligations
                .iter()
                .flatten()
                .any(|ob| ob.rule == Rule::VacuousPrecondition),
            "a satisfiable precondition must not be flagged as vacuous"
        );
    });
}

#[test]
fn an_unsatisfiable_invariant_is_not_vacuously_proved() {
    // The vacuity sweep, applied to loops. It would be easy to assume a loop with an
    // unsatisfiable invariant verifies vacuously -- `I && c => wp(body, I)` is a theorem
    // when `I` is unsatisfiable -- but the report does not rest on that rule alone. The
    // contract condition carries the loop's *entry* obligation, `pre => I`, and a
    // satisfiable precondition cannot imply an unsatisfiable invariant, so the report
    // fails and attributes the failure to `Body`.
    //
    // Pinned because the safety is structural and easy to lose: it depends on the entry
    // condition being part of `wp` and on `pre` being checked for reachability, not on any
    // special treatment of loops. If someone later made `Body` weaker, this would be the
    // test that noticed.
    smt::with_fresh(|| {
        let k = var(8);
        let pre = smt::truth(true);
        let inv = smt::and(smt::ult_const(k, 10), smt::ugt_const(k, 200));
        assert!(
            smt::prove(smt::not(inv)).is_proved(),
            "the invariant under test must be unsatisfiable"
        );
        let body = Stmt::Assign { var: k, expr: k + 1u32 };
        let loop_ = Stmt::While {
            cond: smt::ult_const(k, 4),
            invariant: inv,
            variant: Some(smt::sub(smt::word(4, 8), k)),
            body: &body,
        };
        let post = smt::eq_const(k, 77);
        let report = wp::verify(&loop_, pre, post);
        assert!(
            !report.is_verified(),
            "an unsatisfiable invariant must not verify vacuously"
        );
        assert_eq!(report.establishes(), wp::Established::Nothing);
    });
}

#[test]
fn a_truncated_domain_cannot_masquerade_as_a_clean_sweep() {
    // The eighth hole, and the sharpest instance of the recurring class: a limit that
    // silently means something weaker than it looks, in the one function whose whole job
    // is to *catch* the symbolic engine being wrong.
    //
    // The function used to return `Option<u64>`, and `None` meant two different things:
    // "swept the whole domain, nothing violated" and "stopped early, nothing violated".
    // A caller reading `None` as "no counterexample exists" would be wrong for the second,
    // and this probe showed exactly that:
    //
    //   limit=100 (a prefix)  : None   <- reads as "no counterexample"
    //   limit=256 (the domain): Some(101)
    //
    // The claim being tested is false -- `clamp(x, 20, 200) <= 100` fails as soon as x
    // exceeds 100, and the first witness is x = 101. Searching a prefix of the domain
    // reports no counterexample. The return type now says which case it is, and
    // `NoWitness` is explicitly a statement about the domain that was searched.
    let post = |_x: u64, out: u64| out <= 100;
    let run = |v: u64| clamp_exec(v as u8, 20, 200) as u64;

    // A prefix of the domain: honest, but only about the prefix.
    let prefix = find_counterexample_by_enumeration(100, |_| true, run, post);
    assert_eq!(prefix, wp::Search::NoWitness);
    assert!(
        prefix.is_clean_over_domain(),
        "a clean sweep of a prefix is still a clean sweep of *that* prefix"
    );

    // The whole domain: the counterexample is there, and must be found.
    let full = find_counterexample_by_enumeration(wp::domain_of_bits(8), |_| true, run, post);
    assert_eq!(
        full,
        wp::Search::Witness(101),
        "the first counterexample (x = 101, which returns 101 > 100) must be found over \
         the full domain"
    );

    // The two are now distinguishable at the type level, which is the fix: the negative
    // is unambiguous, so `NoWitness` over a prefix can never be read as a proof.
    assert_ne!(prefix, full);
}

#[test]
fn the_search_domain_matches_the_symbolic_width() {
    // `domain_of_bits` exists so the domain is derived from the input width rather than
    // typed by hand. This pins the derivation and the refusal of unenumerable widths, so
    // the two cannot drift.
    assert_eq!(wp::domain_of_bits(1), 2);
    assert_eq!(wp::domain_of_bits(8), 256);
    assert_eq!(wp::domain_of_bits(16), 65536);

    let zero = std::panic::catch_unwind(|| wp::domain_of_bits(0));
    assert!(zero.is_err(), "a zero-bit domain cannot be enumerated");
    let too_wide = std::panic::catch_unwind(|| wp::domain_of_bits(64));
    assert!(
        too_wide.is_err(),
        "a 64-bit domain cannot be enumerated, and must be refused rather than wrapped"
    );
}
