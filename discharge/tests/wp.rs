//! Verification-condition generation, checked against execution.
//!
//! Two things are tested here, and they are different claims:
//!
//! 1. the *symbolic* proof and a brute-force run of the same function agree, and
//! 2. the *rules* are attributed correctly, so a failure points at the right
//!    clause instead of just reporting `false`.

use discharge::prelude::*;
use discharge::smt::{self, var, Verdict};
use discharge::wp::{self, find_counterexample_by_enumeration, verify, Established, Rule, Stmt};

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
        let (_, count, complete) = wp::obligations(node, post, &mut slots);
        assert_eq!(
            count,
            wp::MAX_OBLIGATIONS,
            "the buffer below the reserved slot should be exactly full"
        );
        // A bare count of `MAX_OBLIGATIONS` is ambiguous -- exactly this many, or a
        // truncated prefix? -- so `obligations` reports completeness too. The same shape
        // as `writes`: a saturated summary must not read as a complete one.
        assert!(!complete, "a truncated set must not report itself complete");
    });
}

#[test]
fn a_complete_obligation_set_reports_itself_complete() {
    // The other half of the truncation fix: a set that fits must say so, or a caller
    // could not tell a genuine `MAX_OBLIGATIONS`-sized set from a truncated one. Without
    // this, `complete == true` would be untested and could silently be always-false.
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
        let node: &'static Stmt<'static> =
            Box::leak(Box::new(Stmt::Seq { first: init, second: loop_ }));
        let mut slots = [None; wp::MAX_OBLIGATIONS + 1];
        let (_, count, complete) = wp::obligations(node, smt::truth(true), &mut slots);
        assert_eq!(count, 2, "preserve and exit");
        assert!(complete, "a set that fits must report itself complete");
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
fn assertions_beyond_the_cap_are_reported_not_hidden() {
    // The assertion arm was the last obligation site still using the silent `push`, on the
    // argument that a dropped assertion is harmless because the backward walk still
    // conjoins it into the weakest precondition. That argument is about `verify`'s
    // *soundness* and it holds -- but `obligations` documents its third return value as
    // `true` only when every side obligation is in the buffer, and for a program with more
    // assertions than the buffer holds it returned `true` while dropping them. The flag was
    // two answers to one question, which is the exact defect the other truncation fixes
    // removed.
    //
    // Both halves are pinned here: the flag must go false, and the report must stop calling
    // itself verified, because a claim whose obligation list is truncated is not a claim
    // that was fully checked. Below the cap nothing changes, so the fix cannot pass by
    // making every assertion-only program fail.
    smt::with_fresh(|| {
        // One assertion per slot, right-nested, all true so only the cap can fail them.
        let build = |n: usize| -> &'static Stmt<'static> {
            let mut node: &'static Stmt<'static> =
                Box::leak(Box::new(Stmt::Assert(smt::truth(true))));
            for _ in 1..n {
                let leaf: &'static Stmt<'static> =
                    Box::leak(Box::new(Stmt::Assert(smt::truth(true))));
                node = Box::leak(Box::new(Stmt::Seq { first: node, second: leaf }));
            }
            node
        };

        // Exactly `MAX_OBLIGATIONS` assertions: the largest set that fits. Complete, and
        // verified -- the reserved slot costs nothing.
        let fits = build(wp::MAX_OBLIGATIONS);
        let mut slots = [None; wp::MAX_OBLIGATIONS + 1];
        let (_, count, complete) = wp::obligations(fits, smt::truth(true), &mut slots);
        assert_eq!(count, wp::MAX_OBLIGATIONS);
        assert!(complete, "a set that fits must report itself complete");
        assert!(
            wp::verify(fits, smt::truth(true), smt::truth(true)).is_verified(),
            "an assertion-only program that fits must still verify"
        );

        // One more assertion than the buffer holds. The flag must go false and the report
        // must refuse, rather than counting 16 and calling the rest checked.
        let over = build(wp::MAX_OBLIGATIONS + 1);
        let mut slots = [None; wp::MAX_OBLIGATIONS + 1];
        let (_, count, complete) = wp::obligations(over, smt::truth(true), &mut slots);
        assert_eq!(count, wp::MAX_OBLIGATIONS, "the buffer below the reserved slot is full");
        assert!(!complete, "a dropped assertion must make the set incomplete");

        let report = wp::verify(over, smt::truth(true), smt::truth(true));
        assert!(
            !report.is_verified(),
            "a report whose obligation list is truncated must not claim verification"
        );
        assert_eq!(report.establishes(), wp::Established::Nothing);
        let (ob, _) = report.first_failure().expect("the truncation must be reported");
        assert_eq!(ob.rule, Rule::ObligationOverflow);

        // And the claim really was truncated: the same program padded well past the cap
        // keeps reporting the truncation instead of saturating quietly.
        let far_over = build(wp::MAX_OBLIGATIONS + 9);
        assert!(
            !wp::verify(far_over, smt::truth(true), smt::truth(true)).is_verified(),
            "padding far past the cap must not verify either"
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

#[test]
fn a_report_does_not_change_its_verdict_after_a_reset() {
    // The thirteenth hole, and the same class as the twelfth but at the top-level verdict:
    // a `Report` records obligations and discharges them *lazily*, each time `is_verified`
    // or `first_failure` is called, against whatever arena is current. A goal is a term id,
    // so after a reset the recorded id named a different formula, and a refuted program
    // could read as verified:
    //
    //   goal id (as recorded): Pred(Term(10))
    //   filler  0: contract discharge = "Counterexample"   <- correct
    //   filler  1: contract discharge = "Valid"            <- a failing report read as proved
    //
    // That is the worst answer this crate can give, on its headline verdict. Obligations
    // now record the arena generation, and `discharge` returns `Unknown` when the arena has
    // moved on, so a stale report fails rather than flips.
    let report = smt::with_fresh(|| {
        let x = var(8);
        let y = var(8);
        let body = Stmt::Assign { var: y, expr: x + 1u32 };
        // Pre: x < 10. Body: y := x+1. Post: y <= 5 -- false for x = 9.
        verify(&body, x.lt_val(10), y.le_val(5))
    });
    assert!(!report.is_verified(), "the contract does not hold, in its own arena");
    assert!(report.contract.is_current(), "freshly built, so current");

    // Every arena, with filler to shift what the recycled id names.
    for n in 0..6 {
        smt::with_fresh(|| {
            for _ in 0..n {
                let _ = smt::truth(true);
            }
            assert!(
                !report.is_verified(),
                "a stale report must never read as verified (filler {})",
                n
            );
            assert!(
                !report.contract.is_current(),
                "after a reset the obligation is no longer current"
            );
            assert!(
                matches!(report.contract.discharge(), Verdict::Unknown),
                "a stale obligation discharges as Unknown, not as a verdict"
            );
            assert!(
                matches!(report.establishes(), Established::Nothing),
                "a stale report establishes nothing"
            );
            assert!(
                report.first_failure().is_some(),
                "a stale report has a failure to report"
            );
        });
    }
}

#[test]
fn a_report_read_in_its_own_arena_is_unchanged() {
    // The teeth. The generation check must not break ordinary use: a report read in the
    // arena that produced it must decide exactly as before, both for a good contract and
    // a bad one.
    smt::with_fresh(|| {
        let x = var(8);
        let y = var(8);
        let body = Stmt::Assign { var: y, expr: x + 1u32 };
        let good = verify(&body, x.lt_val(10), y.le_val(10));
        assert!(good.is_verified(), "{:?}", good.first_failure());
        assert!(good.contract.is_current());
        assert!(matches!(good.contract.discharge(), Verdict::Valid));
        // No loops, so termination is trivial and the report is Total. (I wrote Partial
        // first; the run corrected me.)
        assert!(matches!(good.establishes(), Established::Total));
    });
    smt::with_fresh(|| {
        let x = var(8);
        let y = var(8);
        let body = Stmt::Assign { var: y, expr: x + 1u32 };
        let bad = verify(&body, x.lt_val(10), y.le_val(5));
        assert!(!bad.is_verified());
        assert!(matches!(bad.contract.discharge(), Verdict::Counterexample(_)));
    });
}

// ---------------------------------------------------------------------------
// The SMT-LIB export must not invert a goal, and must be well-sorted.
//
// A boolean is a one-bit word in this engine, so the printer has to coerce it. The
// coercion used to print `(= w (_ bv0 1))` while its own comment said `w != 0` -- the
// negation. A constant goal therefore came out inverted: `truth(false)` was written as
// `(assert false)`, which every solver calls `unsat`, so an external checker would report
// an impossible obligation as *proved*. The operator choice was wrong too: a boolean
// connective at width 1 was printed with the bit-vector operator, so `not(x == y)` became
// `(bvnot (= x y))`, which is ill-sorted.
// ---------------------------------------------------------------------------

#[test]
fn the_export_does_not_invert_a_constant_goal() {
    smt::with_fresh(|| {
        let q = Query::new(&[], smt::truth(false));
        let text = q.to_smtlib2_string();
        // The goal is `false`; its negation is `true`, and a solver would answer `sat`.
        // The buggy printer wrote the goal as `(= 0 0)` (= true), whose negation is false.
        assert!(
            !text.contains("(= (_ bv0 1) (_ bv0 1))"),
            "a constant-false goal must not be exported as `(= 0 0)`:\n{}",
            text
        );
        assert!(
            text.contains("(distinct (_ bv0 1) (_ bv0 1))"),
            "a one-bit word as a proposition must be `distinct` from zero:\n{}",
            text
        );

        let q = Query::new(&[], smt::truth(true));
        let text = q.to_smtlib2_string();
        assert!(
            text.contains("(distinct (_ bv1 1) (_ bv0 1))"),
            "a constant-true goal must export as `1 != 0`:\n{}",
            text
        );
    });
}

#[test]
fn the_export_uses_boolean_operators_for_booleans() {
    smt::with_fresh(|| {
        let x = var(8);
        let y = var(8);
        let vars = [x, y];

        // `not(x == y)` is a boolean; its operand is a boolean. `bvnot` would be ill-sorted.
        let q = Query::new(&vars, smt::not(smt::eq(x, y)));
        let text = q.to_smtlib2_string();
        assert!(
            text.contains("(not (= x0_8 x1_8))"),
            "a negated comparison must use the boolean `not`:\n{}",
            text
        );
        assert!(
            !text.contains("bvnot"),
            "a boolean must not be printed with a bit-vector operator:\n{}",
            text
        );

        // `implies` is `!a || b`, both booleans.
        let q = Query::new(&vars, smt::implies(smt::eq(x, y), smt::ult(x, y)));
        let text = q.to_smtlib2_string();
        assert!(
            text.contains("(or (not (= x0_8 x1_8)) (bvult x0_8 x1_8))"),
            "an implication must be printed as a boolean `or` of booleans:\n{}",
            text
        );

        // A wider conjunction is still a bit-vector operation.
        let wide = smt::band(x, y);
        let q = Query::new(&vars, smt::eq(wide, x));
        let text = q.to_smtlib2_string();
        assert!(
            text.contains("(bvand x0_8 x1_8)"),
            "a wide bitwise and must stay `bvand`:\n{}",
            text
        );
    });
}

#[test]
fn the_export_widens_with_zero_extend() {
    // `truncate` changes a width in either direction. Narrowing keeps the low bits
    // (`extract`), but widening zero-fills, and `extract w-1 0` on a narrower operand is
    // ill-sorted: extracting bit 15 from an 8-bit vector. The export used `extract` for
    // both, so a widening `truncate` produced a file no solver accepts.
    smt::with_fresh(|| {
        let x = var(8);

        let wide = smt::truncate(x, 16);
        let text = Query::new(&[x], smt::eq(wide, smt::word(255, 16))).to_smtlib2_string();
        assert!(
            text.contains("((_ zero_extend 8) x0_8)"),
            "a widening truncate must zero-extend:\n{}",
            text
        );
        assert!(
            !text.contains("extract 15 0"),
            "a widening truncate must not extract bits the source does not have:\n{}",
            text
        );

        let narrow = smt::truncate(x, 3);
        let text = Query::new(&[x], smt::eq(narrow, smt::word(5, 3))).to_smtlib2_string();
        assert!(
            text.contains("((_ extract 2 0) x0_8)"),
            "a narrowing truncate must still extract the low bits:\n{}",
            text
        );
    });
}

// ---------------------------------------------------------------------------
// A constant that does not fit its width is a mistake, not a value to wrap.
//
// `x + 300u32` on a `u8` used to build the same term as `x + 44`: `word` truncated the
// literal silently, and the proof then said something true about a constant nobody wrote.
// `eq_const` already refuses an out-of-range constant, so the two spellings of the same
// intent disagreed. `word` now marks the term, and the query answers `Unknown`.
// ---------------------------------------------------------------------------

#[test]
fn a_constant_that_does_not_fit_its_width_is_not_wrapped() {
    // `eq_const` already handles this one honestly and *decides* it: no 8-bit value
    // equals 300, so the predicate is unsatisfiable. That is a real answer, not a refusal.
    smt::with_fresh(|| {
        let x = var(8);
        assert_eq!(smt::prove(x.eq_val(300)), Verdict::Unsat);
    });
    // The DSL spelling used to wrap: `x + 300u32` built the same term as `x + 44`, so
    // `sum == 44` came back as a counterexample instead of a refusal. It must refuse.
    smt::with_fresh(|| {
        let x = var(8);
        let sum = x + 300u32;
        assert_eq!(smt::prove(sum.eq_val(44)), Verdict::Unknown);
        assert_eq!(smt::prove(sum.eq_val(300)), Verdict::Unknown);
    });
    // `word` itself, for the same reason.
    smt::with_fresh(|| {
        assert_eq!(smt::prove(smt::word(300, 8).eq_val(44)), Verdict::Unknown);
    });
}

#[test]
fn a_constant_that_fits_is_unaffected() {
    smt::with_fresh(|| {
        let x = var(8);
        // In-range literals, including the exact maximum, still decide normally.
        assert_eq!(smt::prove((x + 44u32).eq_val(44).implies(x.eq_val(0))), Verdict::Valid);
        assert_eq!(smt::prove((x & 0xffu32).le_val(255)), Verdict::Valid);
        assert_eq!(smt::prove(smt::word(255, 8).le_val(255)), Verdict::Valid);
        assert_eq!(smt::prove(smt::word(0, 8).eq_val(0)), Verdict::Valid);
    });
}

// ---------------------------------------------------------------------------
// An unsatisfiable `Assume` makes everything after it vacuous.
//
// `Assume(false); y := 0` with postcondition `y == 99` used to come back `verified` and
// `Total`: `false => wp(y := 0, y == 99)` is a theorem, so every obligation discharged and
// the report claimed a proof of code no run can reach. This is the vacuity class one level
// down from `VacuousPrecondition` -- the precondition is reachable, but a statement inside
// the body cuts the path off. A *reachable* `Assume` is a normal modelling tool and must
// still verify, so the check is "this Assume cannot hold", not "there is an Assume".
// ---------------------------------------------------------------------------

#[test]
fn an_unreachable_assume_is_not_a_proof() {
    smt::with_fresh(|| {
        let y = var(8);
        let s = Stmt::Seq {
            first: &Stmt::Assume(smt::truth(false)),
            second: &Stmt::Assign { var: y, expr: smt::word(0, 8) },
        };
        let r = verify(&s, smt::truth(true), y.eq_val(99));
        assert!(!r.is_verified(), "an unreachable assume certified y == 99");
        assert_eq!(r.establishes(), Established::Nothing);
        let (ob, v) = r.first_failure().expect("a failure was expected");
        assert_eq!(ob.rule, Rule::VacuousAssume);
        assert!(!v.is_proved());
    });
}

#[test]
fn a_contradicting_assume_is_caught() {
    smt::with_fresh(|| {
        let y = var(8);
        // The first assume is reachable; the second contradicts it, so the path dies here.
        let s = Stmt::Seq {
            first: &Stmt::Assume(y.lt_val(10)),
            second: &Stmt::Assume(smt::and(y.lt_val(10), y.gt_val(100))),
        };
        let r = verify(&s, smt::truth(true), y.eq_val(99));
        assert!(!r.is_verified());
        assert_eq!(r.first_failure().unwrap().0.rule, Rule::VacuousAssume);
    });
}

#[test]
fn a_reachable_assume_still_verifies() {
    smt::with_fresh(|| {
        let y = var(8);
        let s = Stmt::Seq {
            first: &Stmt::Assume(y.lt_val(10)),
            second: &Stmt::Assign { var: y, expr: y },
        };
        let r = verify(&s, smt::truth(true), y.lt_val(10));
        assert!(r.is_verified(), "a reachable assume must not be refused");
        assert_eq!(r.establishes(), Established::Total);
    });
}

#[test]
fn a_duplicated_assign_many_target_is_refused_not_ordered() {
    // `x := 1, x := 2` as a *simultaneous* assignment has no single meaning: keeping the
    // last proves `x == 2`, keeping the first proves `x == 1`, and which one you get is
    // list order rather than anything the specification says. The only safe answer is
    // `Unknown`, and it must hold in release builds too, where the `debug_assert!` that
    // guards `AssignMany` is compiled out. This pins the behavior at the `wp` layer; the
    // `smt` layer is pinned by `smt::subst_tests::two_bindings_for_one_target_are_refused`.
    smt::with_fresh(|| {
        let x = var(8);
        let binds = [(x, smt::word(1, 8)), (x, smt::word(2, 8))];
        let s = Stmt::AssignMany { binds: &binds };
        // Whichever way the list is read, the *other* postcondition would be "proved".
        for post in [x.eq_val(1), x.eq_val(2)] {
            let pre = wp::wp(post, &s);
            assert_eq!(
                smt::prove(pre),
                smt::Verdict::Unknown,
                "a duplicated target must not be resolved by list order"
            );
        }
    });
}

#[test]
fn distinct_assign_many_targets_still_work() {
    // The refusal above must not come from refusing every `AssignMany`.
    smt::with_fresh(|| {
        let x = var(8);
        let y = var(8);
        let binds = [(x, smt::word(1, 8)), (y, smt::word(2, 8))];
        let s = Stmt::AssignMany { binds: &binds };
        let pre = wp::wp(smt::and(x.eq_val(1), y.eq_val(2)), &s);
        assert_eq!(smt::prove(pre), smt::Verdict::Valid);
    });
}

#[test]
fn an_assertion_is_checked_under_the_guard_that_reaches_it() {
    // `if x == 1 { assert x == 1 }` is correct: the assertion is only reached when the
    // guard holds. It used to be reported as a failure, because the assertion was checked
    // against every `x` instead of the `x` the guard admits -- so a correct program could
    // not use an assertion inside a branch at all.
    smt::with_fresh(|| {
        let x = var(8);
        let guard = x.eq_val(1);
        let s = Stmt::If {
            cond: guard,
            then_: &Stmt::Assert(guard),
            else_: &Stmt::Skip,
        };
        let r = verify_program(&s, smt::truth(true), smt::truth(true));
        assert!(r.is_verified(), "a guarded assertion must not be refused");
    });
}

#[test]
fn both_branches_see_their_own_guard() {
    smt::with_fresh(|| {
        let x = var(8);
        let guard = x.eq_val(1);
        let s = Stmt::If {
            cond: guard,
            then_: &Stmt::Assert(guard),
            else_: &Stmt::Assert(smt::not(guard)),
        };
        let r = verify_program(&s, smt::truth(true), smt::truth(true));
        assert!(r.is_verified(), "each branch must see its own guard");
    });
}

#[test]
fn a_false_assertion_inside_a_branch_is_still_caught() {
    // The teeth for the fix above: widening the context must not turn a real failure into
    // a green check. `assert x == 2` under `x == 1` is false, and a write inside the branch
    // must not be substituted into the guard either.
    smt::with_fresh(|| {
        let x = var(8);
        let s = Stmt::If {
            cond: x.eq_val(1),
            then_: &Stmt::Assert(x.eq_val(2)),
            else_: &Stmt::Skip,
        };
        let r = verify_program(&s, smt::truth(true), smt::truth(true));
        assert!(!r.is_verified(), "a false assertion must not verify");
        assert_eq!(r.first_failure().unwrap().0.rule, Rule::Assertion);
    });

    smt::with_fresh(|| {
        let x = var(8);
        // `if x == 1 { x := 5; assert x == 1 }`: the guard is about the *entry* state, so
        // substituting the write into it would make this vacuously true.
        let inner = Stmt::Seq {
            first: &Stmt::Assign { var: x, expr: smt::word(5, 8) },
            second: &Stmt::Assert(x.eq_val(1)),
        };
        let s = Stmt::If {
            cond: x.eq_val(1),
            then_: &inner,
            else_: &Stmt::Skip,
        };
        let r = verify_program(&s, smt::truth(true), smt::truth(true));
        assert!(!r.is_verified(), "the guard must not be rewritten by the branch");
    });
}

#[test]
fn a_dominating_assume_is_context_for_a_later_assertion() {
    smt::with_fresh(|| {
        let x = var(8);
        let fact = x.eq_val(7);
        let s = Stmt::Seq {
            first: &Stmt::Assume(fact),
            second: &Stmt::Assert(fact),
        };
        let r = verify_program(&s, smt::truth(true), smt::truth(true));
        assert!(r.is_verified(), "an assumed fact may be asserted");

        // And the reverse order must not: the assertion runs before the assume, so the
        // assume cannot reach back and justify it.
        let s = Stmt::Seq {
            first: &Stmt::Assert(fact),
            second: &Stmt::Assume(fact),
        };
        let r = verify_program(&s, smt::truth(true), smt::truth(true));
        assert!(!r.is_verified(), "an assume must not justify an earlier assertion");
    });
}

#[test]
fn an_assertion_in_a_loop_body_sees_the_invariant_and_guard() {
    smt::with_fresh(|| {
        let i = var(8);
        // while i < 10 invariant i <= 10 { assert i <= 10 }
        let body = Stmt::Assert(i.le_val(10));
        let s = Stmt::While {
            cond: i.lt_val(10),
            invariant: i.le_val(10),
            variant: None,
            body: &body,
        };
        let r = verify(&s, i.le_val(10), i.le_val(10));
        assert!(r.is_verified(), "the invariant is the context of the body");

        // Teeth: an assertion the invariant does not imply must still fail, even though
        // the loop obligations themselves are fine.
        let bad = Stmt::Assert(i.le_val(3));
        let s = Stmt::While {
            cond: i.lt_val(10),
            invariant: i.le_val(10),
            variant: None,
            body: &bad,
        };
        let r = verify(&s, i.le_val(10), i.le_val(10));
        assert!(!r.is_verified(), "an unimplied assertion must not verify");
    });
}

#[test]
fn an_assertion_after_an_if_sees_the_if() {
    // `if c { A } else { B }; assert g` is only reached in a state the `if` can produce,
    // so the claim is `wp(if, g)`. It used to be checked as if the `if` were absent, so
    // this correct program was reported as a failure even though the contract obligation
    // proved it.
    smt::with_fresh(|| {
        let x = var(8);
        let branch = Stmt::If {
            cond: x.eq_val(1),
            then_: &Stmt::Assign { var: x, expr: smt::word(1, 8) },
            else_: &Stmt::Assign { var: x, expr: smt::word(2, 8) },
        };
        let s = Stmt::Seq {
            first: &branch,
            second: &Stmt::Assert(smt::or(x.eq_val(1), x.eq_val(2))),
        };
        let r = verify_program(&s, smt::truth(true), smt::truth(true));
        assert!(r.is_verified(), "the `if` must reach the assertion after it");

        // Teeth: a claim the branches do not both establish must still fail.
        let s = Stmt::Seq {
            first: &branch,
            second: &Stmt::Assert(x.eq_val(1)),
        };
        let r = verify_program(&s, smt::truth(true), smt::truth(true));
        assert!(!r.is_verified(), "one branch leaves x == 2, so x == 1 fails");
    });
}

#[test]
fn an_assertion_after_a_loop_sees_the_loop() {
    // The loop analogue of `an_assertion_after_an_if_sees_the_if`, and the same defect one
    // construct over: an assertion to the *right* of a loop was checked in the pre-loop
    // state. `while x < 3 inv x <= 3 { x := x + 1 }; assert x >= 3` was reported as a
    // failure (with counterexample `x = 0`, the entry state) even though the loop's own
    // `LoopExit` obligation proves the claim at every state the loop can leave. A claim
    // after a loop is only made for the states the loop can produce, so it is checked
    // under `invariant && !guard`.
    smt::with_fresh(|| {
        let x = var(8);
        let body = Stmt::Assign { var: x, expr: smt::add(x, smt::word(1, 8)) };
        let l = Stmt::While {
            cond: x.lt_val(3),
            invariant: x.le_val(3),
            variant: None,
            body: &body,
        };
        let s = Stmt::Seq {
            first: &l,
            second: &Stmt::Assert(x.ge_val(3)),
        };
        let r = verify_program(&s, x.le_val(3), x.le_val(3));
        assert!(
            r.is_verified(),
            "the loop must reach the assertion after it; obligations were {:?}",
            r.obligations.iter().flatten().map(|o| (o.rule, o.discharge())).collect::<Vec<_>>()
        );

        // Teeth: a claim the loop's exit does not establish must still fail. `x <= 3` is the
        // invariant, so `x < 3` is not implied by the exit state `x == 3`.
        let s = Stmt::Seq {
            first: &l,
            second: &Stmt::Assert(x.lt_val(3)),
        };
        let r = verify_program(&s, x.le_val(3), x.le_val(3));
        assert!(!r.is_verified(), "the loop exits at x == 3, so x < 3 fails");

        // And the exit context is the *invariant* plus the failed guard, not the guard
        // itself: `x >= 3` holds at the exit even though nothing else does.
        let s = Stmt::Seq {
            first: &l,
            second: &Stmt::Assert(x.le_val(3)),
        };
        let r = verify_program(&s, x.le_val(3), x.le_val(3));
        assert!(r.is_verified(), "the invariant still holds after the loop");
    });
}

#[test]
fn a_claim_after_a_loop_inside_a_branch_is_still_checked() {
    // The combination of the `if` rewrite (DEFECT 37) and the loop rewrite (DEFECT 40): a
    // claim after a loop that is itself inside a branch. Both rewrites must apply, and the
    // loop's own `LoopExit` obligation is the independent backstop -- it is `inv && !guard
    // => q`, so it catches a false claim even if the rewrite were wrong. This case is here
    // because "fix one construct" twice in a row is how the family got its members, and the
    // composition is where a fix for one can silently undo the other.
    smt::with_fresh(|| {
        let x = var(8);
        let body = Stmt::Assign { var: x, expr: smt::add(x, smt::word(1, 8)) };
        let l = Stmt::While {
            cond: x.lt_val(3),
            invariant: x.le_val(3),
            variant: None,
            body: &body,
        };
        // if x == 0 { while x < 3 inv x <= 3 { x := x + 1 }; assert x >= 3 } else skip
        let inner = Stmt::Seq {
            first: &l,
            second: &Stmt::Assert(x.ge_val(3)),
        };
        let prog = Stmt::If { cond: x.eq_val(0), then_: &inner, else_: &Stmt::Skip };
        let r = verify_program(&prog, x.le_val(3), x.le_val(3));
        assert!(r.is_verified(), "nested loop claim must verify; got {:?}", r.first_failure());

        // Teeth: a false claim inside the branch must still fail. It is caught by `LoopExit`
        // (`x == 5` is not implied by the exit state `x == 3`), so this also checks that the
        // loop rewrite did not weaken `LoopExit` while making the assertion pass.
        let bad = Stmt::Seq {
            first: &l,
            second: &Stmt::Assert(x.eq_val(5)),
        };
        let prog = Stmt::If { cond: x.eq_val(0), then_: &bad, else_: &Stmt::Skip };
        let r = verify_program(&prog, x.le_val(3), x.le_val(3));
        assert!(
            !r.is_verified(),
            "x == 5 is not implied by the loop exit, so it must fail"
        );
    });
}

#[test]
fn a_nested_if_reaches_an_assertion_after_both() {
    smt::with_fresh(|| {
        let x = var(8);
        let inner = Stmt::If {
            cond: x.eq_val(1),
            then_: &Stmt::Assign { var: x, expr: smt::word(1, 8) },
            else_: &Stmt::Assign { var: x, expr: smt::word(2, 8) },
        };
        let outer = Stmt::If {
            cond: x.eq_val(1),
            then_: &Stmt::Assign { var: x, expr: smt::word(3, 8) },
            else_: &inner,
        };
        let g = smt::or(x.eq_val(1), smt::or(x.eq_val(2), x.eq_val(3)));
        let s = Stmt::Seq {
            first: &outer,
            second: &Stmt::Assert(g),
        };
        let r = verify_program(&s, smt::truth(true), smt::truth(true));
        assert!(r.is_verified(), "nesting must compose");
    });
}

#[test]
fn a_nested_loop_cannot_make_the_outer_variant_look_healthy() {
    // `while i < 100 { i := i + 1; while i != 0 { i := 0 } }` never terminates: the
    // inner loop resets `i` on every outer iteration, so the outer counter makes no
    // progress. The inner loop's body writes `i`, so `i` has an unknown value after it,
    // and the outer measure `100 - i` must therefore be refuted.
    //
    // This used to be *proved*. `variant_after` read a nested `While` as leaving the
    // measure alone, so the obligation reduced to `100 - (i + 1) < 100 - i`, which is
    // valid -- and the report claimed `Total` for a program that does not halt. A
    // termination proof for a divergent program is the exact claim this crate exists to
    // make honestly, so this is a soundness regression test, not a feature test.
    smt::with_fresh(|| {
        let i = var(8);
        let inner_body = Stmt::Assign { var: i, expr: smt::word(0, 8) };
        let inner = Stmt::While {
            cond: smt::not(i.eq_val(0)),
            invariant: i.le_val(100),
            variant: None,
            body: &inner_body,
        };
        let bump = Stmt::Assign { var: i, expr: i + 1u32 };
        let outer_body = Stmt::Seq { first: &bump, second: &inner };
        let measure = smt::sub(smt::word(100, 8), i);
        let ob = wp::termination_obligation(i.lt_val(100), i.le_val(100), measure, &outer_body);
        assert!(
            !ob.discharge().is_proved(),
            "a nested loop that resets the outer counter must not yield a termination proof"
        );
    });
}

#[test]
fn a_nested_loop_that_leaves_the_measure_alone_still_proves() {
    // The control, and the reason the fix havocs only what the inner body writes rather
    // than the whole state. `while i < 100 { i := i + 1; while j != 0 { j := 0 } }`
    // terminates: the inner loop cannot touch `i`. The outer measure `100 - i` must still
    // be proved, or the fix would have replaced a soundness hole with a loss of the
    // common nested-loop shape (an inner scan under an outer counter).
    smt::with_fresh(|| {
        let i = var(8);
        let j = var(8);
        let inner_body = Stmt::Assign { var: j, expr: smt::word(0, 8) };
        let inner = Stmt::While {
            cond: smt::not(j.eq_val(0)),
            invariant: j.le_val(100),
            variant: None,
            body: &inner_body,
        };
        let bump = Stmt::Assign { var: i, expr: i + 1u32 };
        let outer_body = Stmt::Seq { first: &bump, second: &inner };
        let measure = smt::sub(smt::word(100, 8), i);
        let ob = wp::termination_obligation(i.lt_val(100), i.le_val(100), measure, &outer_body);
        assert!(
            ob.discharge().is_proved(),
            "an inner loop that does not write the measured variable must not break the proof"
        );
    });
}

#[test]
fn an_over_cap_nested_loop_havocs_the_measure_instead_of_leaving_it_alone() {
    // `writes` records at most `MAX_WRITES` variables and flags the frame *incomplete*
    // beyond that. The nested-loop arm of `variant_after` must read an incomplete frame as
    // "the effect is unknown" and havoc the measure -- not fall through to substituting the
    // recorded prefix, which for a measure *outside* that prefix is a no-op. The no-op is
    // the old soundness hole: a nested loop whose body can write the measure would look
    // like it leaves the measure alone, so `V' < V` would be discharged from `V < V`.
    // The verdict is refuted under both readings here, so only the returned *term*
    // distinguishes them -- which is exactly what this pins, and why it has to assert on
    // the term rather than on `is_proved`.
    smt::with_fresh(|| {
        let vars: Vec<Var> = (0..20).map(|_| var(4)).collect();
        let binds: Vec<(Var, Var)> = vars.iter().map(|v| (*v, smt::word(0, 4))).collect();
        let body = Stmt::AssignMany { binds: &binds };
        let frame = wp::writes(&body);
        assert_eq!(frame.len(), 16, "the frame must fill to the cap");
        assert!(!frame.complete(), "20 writes must be flagged incomplete");

        let nested = Stmt::While {
            cond: smt::ult_const(vars[18], 100),
            invariant: smt::truth(true),
            variant: None,
            body: &body,
        };
        // A measure the truncated frame never recorded. Substituting the prefix leaves it
        // untouched; the honest answer is a fresh, unconstrained value.
        let beyond = vars[18];
        let after = wp::variant_after(&nested, beyond);
        assert_ne!(
            after, beyond,
            "an incomplete frame must havoc the measure, not leave it unchanged"
        );
        // And that havoc really does defeat the termination obligation.
        let ob = wp::termination_obligation(
            smt::ult_const(beyond, 100),
            smt::truth(true),
            beyond,
            &nested,
        );
        assert!(
            !ob.discharge().is_proved(),
            "a measure that the nested body may write must not yield a termination proof"
        );
    });
}
