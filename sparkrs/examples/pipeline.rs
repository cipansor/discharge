//! The full pipeline: a program, its verification conditions, their proofs, and
//! an SMT-LIB2 export for independent checking.
//!
//! This is the shape a SPARK user works in: state a contract, describe the body,
//! let the tool generate the obligations, read a verdict per obligation, and hand
//! anything the built-in engine cannot decide to a solver.
//!
//! Run with: `cargo run --features std --example pipeline`

use sparkrs::prelude::*;
use sparkrs::smt::{self, var, Verdict};
use sparkrs::wp::{self, Stmt};

/// A bounded accumulator, the shape of loop that shows up in a controller:
///
/// ```text
/// sum := 0
/// i := 0
/// while i < n {
///     sum := sum + step
///     i := i + 1
/// }
/// ```
///
/// The safety property is `sum <= n * step`. Proving it needs an invariant that
/// links `sum` and `i`; `sum == i * step` is the one that works, and inventing it
/// is the human's job.
///
/// Everything is modelled at 4 bits so the multiplier stays inside the BDD's
/// comfortable range. At 8 bits the *same* proof returns `Unknown`, which is a
/// real limit of this engine and is demonstrated in
/// `cargo run --features std --example flight_control`.
fn main() {
    println!("=== verification conditions for a bounded accumulator ===\n");

    let (report, text) = smt::with_fresh(|| {
        let sum = var(4);
        let i = var(4);
        let n = var(4);
        let step = var(4);

        // `n` and `step` are bounded so that n * step stays inside 4 bits.
        let pre = smt::and(n.le_val(3), step.le_val(3));

        let init_sum = Stmt::Assign { var: sum, expr: smt::word(0, 4) };
        let init_i = Stmt::Assign { var: i, expr: smt::word(0, 4) };
        let bump_sum = Stmt::Assign { var: sum, expr: sum + step };
        let bump_i = Stmt::Assign { var: i, expr: i + 1u32 };
        let body = Stmt::Seq { first: &bump_sum, second: &bump_i };

        // The invariant carries the arithmetic link. Drop it and the proof fails.
        let inv = smt::and(i.le(n), sum.eq(smt::mul(i, step)));
        let loop_ = Stmt::While {
            cond: i.lt(n),
            invariant: inv,
            // `n - i` decreases by one per iteration, so the loop terminates.
            variant: Some(smt::sub(n, i)),
            body: &body,
        };
        let prog = Stmt::Seq {
            first: &init_sum,
            second: &Stmt::Seq { first: &init_i, second: &loop_ },
        };

        let post = sum.le(smt::mul(n, step));
        let report = wp::verify(&prog, pre, post);

        // Export the contract obligation for an independent solver. Declaring the
        // variables matters: without them the text would be unreadable and
        // unusable, which is the whole point of the export.
        let vars = [sum, i, n, step];
        let q = Query::new(&vars, report.contract.goal);
        let text = q.to_smtlib2_string();
        (report, text)
    });

    println!("obligations generated: {}", report.count);
    for (idx, ob) in report.obligations.iter().take(report.count).flatten().enumerate() {
        println!("  [{}] {:?}: {}", idx + 1, ob.rule, short(&ob.discharge()));
    }
    println!(
        "  [contract] {:?}: {}",
        report.contract.rule,
        short(&report.contract.discharge())
    );
    println!();
    if report.is_verified() {
        println!("all obligations discharged by the embedded engine");
        println!(
            "correctness: {:?} (every loop carried a variant)\n",
            report.correctness()
        );
    } else {
        println!("engine did not discharge everything\n");
    }

    println!("the contract as SMT-LIB2, for independent checking:\n");
    for line in text.lines() {
        println!("  {}", line);
    }
    println!();

    // ---------------------------------------------------------------------
    // The same loop with a too-weak invariant, so the failure is legible.
    // ---------------------------------------------------------------------
    println!("=== the same loop with a too-weak invariant ===\n");

    let bad = smt::with_fresh(|| {
        let sum = var(4);
        let i = var(4);
        let n = var(4);
        let step = var(4);
        let pre = smt::and(n.le_val(3), step.le_val(3));

        let init_sum = Stmt::Assign { var: sum, expr: smt::word(0, 4) };
        let init_i = Stmt::Assign { var: i, expr: smt::word(0, 4) };
        let bump_sum = Stmt::Assign { var: sum, expr: sum + step };
        let bump_i = Stmt::Assign { var: i, expr: i + 1u32 };
        let body = Stmt::Seq { first: &bump_sum, second: &bump_i };

        // `i <= n` alone says nothing about `sum`, so the exit condition
        // `i >= n => sum <= n * step` cannot follow from it.
        let loop_ = Stmt::While {
            cond: i.lt(n),
            invariant: i.le(n),
            variant: None,
            body: &body,
        };
        let prog = Stmt::Seq {
            first: &init_sum,
            second: &Stmt::Seq { first: &init_i, second: &loop_ },
        };
        let post = sum.le(smt::mul(n, step));
        let report = wp::verify(&prog, pre, post);

        let text = {
            let vars = [sum, i, n, step];
            let q = Query::new(&vars, report.contract.goal);
            q.to_smtlib2_string()
        };
        (report, text)
    });

    let (bad_report, bad_text) = bad;
    match bad_report.first_failure() {
        None => println!("unexpectedly verified"),
        Some((ob, verdict)) => {
            println!("failed rule: {:?}", ob.rule);
            println!("verdict: {}", verdict);
            println!(
                "correctness: {:?} (the variant is still proved, but the exit condition is not)",
                bad_report.correctness()
            );
            if let Verdict::Counterexample(c) = verdict {
                println!("witness: {}", c);
            }
        }
    }
    println!("\nand the obligation a solver would be handed:\n");
    for line in bad_text.lines() {
        println!("  {}", line);
    }

    // ---------------------------------------------------------------------
    // The macro layer, for obligations that do not need a program.
    // ---------------------------------------------------------------------
    println!("\n=== one-line obligations via macros ===\n");
    smt::with_fresh(|| {
        let x = var(8);

        // These panic with the verdict if the obligation does not hold.
        verify!(x.le_val(255));
        println!("verify!  x <= 255 for u8               : ok");
        verify!((x & 0x0fu32).lt_val(16));
        println!("verify!  (x & 0x0f) < 16              : ok");

        let v = contract! { requires x.lt_val(16), ensures x.lt_val(32) };
        println!("contract! x < 16 ==> x < 32            : {}", short(&v));

        // `proof!` returns a kernel certificate, or panics. Reaching the next
        // line is itself the proof.
        let cert = proof!(x.le_val(255));
        let wrapped = Verified::from_certificate(7u8, cert);
        match wrapped {
            Some(v) => println!("proof!  certificate accepted, value    : {}", v.get()),
            None => println!("proof!  certificate was stale, refused"),
        }

        // A runtime check on a concrete value, no solver involved.
        let _ = check!(contract::Pred::Le(255), 200u64);
        println!("check!   runtime precondition on 200   : ok");
    });

    println!("\ndone");
}

fn short(v: &Verdict) -> &'static str {
    match v {
        Verdict::Valid => "valid",
        Verdict::Counterexample(_) => "refuted",
        Verdict::Unknown => "unknown",
        Verdict::Unsat => "unsat",
    }
}
