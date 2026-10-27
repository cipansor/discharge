//! Modular verification: procedures checked once, calls reasoned about through
//! contracts.
//!
//! Without contracts, every call would have to be verified by inlining the callee's
//! body — which is exponential in the call graph and impossible for recursion. With
//! them, a procedure is proved once against its own contract, and each call site
//! costs only two implications.
//!
//! Run with: `cargo run --features std --example contracts`

use discharge::smt::{self, var, Verdict};
use discharge::wp::{self, Proc, Rule, Stmt};

/// `sat_inc`: requires `x <= 20`, ensures `r <= 20 && (x < 20 => r == x + 1)`.
///
/// A saturating increment. It is the interesting example because the *bound* in its
/// postcondition, not the equation, is what a caller's loop invariant will need.
fn main() {
    println!("=== a procedure and its contract ===\n");

    smt::with_fresh(|| {
        let x = var(8);
        let r = var(8);
        let body = Stmt::Assign {
            var: r,
            expr: smt::ite(x.lt_val(20), x + 1u32, smt::word(20, 8)),
        };
        let sat_inc = Proc {
            name: "sat_inc",
            requires: smt::ule_const(x, 20),
            ensures: smt::and(
                smt::ule_const(r, 20),
                smt::implies(x.lt_val(20), smt::eq(r, x + 1u32)),
            ),
            body: &body,
        };

        // The "once" half: prove the body meets the contract.
        let callee = wp::verify_proc(&sat_inc);
        println!("sat_inc (the callee, checked once)");
        println!("  requires : x <= 20");
        println!("  ensures  : r <= 20 && (x < 20 => r == x + 1)");
        println!("  verified : {}", callee.is_verified());
        println!();
        println!("From here on, no caller ever looks at that body again.\n");

        // The "many" half: a caller, and a caller that gets it wrong.
        let a = var(8);
        let tmp = var(8);
        let actuals = [(x, a), (r, tmp)];
        let writes = [r];
        let call = Stmt::Call { proc_: &sat_inc, actuals: &actuals, writes: &writes };

        // In range: verifies.
        let good_init = Stmt::Assign { var: a, expr: smt::word(3, 8) };
        let good = Stmt::Seq { first: &good_init, second: &call };
        let rep = wp::verify(&good, smt::truth(true), smt::ule_const(tmp, 20));
        println!("caller: a := 3; t := sat_inc(a); assert t <= 20");
        println!("  verified : {} ({} obligation)", rep.is_verified(), rep.count);
        println!();

        // Out of range: the caller's fault, and reported as such.
        let bad_init = Stmt::Assign { var: a, expr: smt::word(200, 8) };
        let bad = Stmt::Seq { first: &bad_init, second: &call };
        let rep = wp::verify(&bad, smt::truth(true), smt::ule_const(tmp, 20));
        println!("caller: a := 200; t := sat_inc(a)   // precondition is x <= 20");
        println!("  verified : {}", rep.is_verified());
        match rep.first_failure() {
            Some((ob, _)) => {
                println!("  failed   : {:?}", ob.rule);
                println!("             the fault is the caller's, not the callee's");
            }
            None => println!("  unexpectedly verified"),
        }
        println!();
    });

    // ---------------------------------------------------------------------
    // A call inside a loop. This is where a postcondition stops being
    // bookkeeping and becomes load-bearing.
    // ---------------------------------------------------------------------
    println!("=== a call inside a loop, where the postcondition is load-bearing ===\n");

    smt::with_fresh(|| {
        let x = var(8);
        let r = var(8);
        let body = Stmt::Assign {
            var: r,
            expr: smt::ite(x.lt_val(20), x + 1u32, smt::word(20, 8)),
        };
        let sat_inc = Proc {
            name: "sat_inc",
            requires: smt::ule_const(x, 20),
            ensures: smt::and(
                smt::ule_const(r, 20),
                smt::implies(x.lt_val(20), smt::eq(r, x + 1u32)),
            ),
            body: &body,
        };
        // The weaker contract, for comparison below.
        let weak = Proc {
            name: "sat_inc_weak",
            requires: smt::ule_const(x, 20),
            ensures: smt::implies(x.lt_val(20), smt::eq(r, x + 1u32)),
            body: &body,
        };

        println!("for k := 0; k < 4; k += 1 {{ t := sat_inc(a); a := t }}");
        println!("invariant: a <= 20 && k <= 4\n");

        let run = |proc_: &Proc<'_>| {
            let a = var(8);
            let k = var(3);
            let tmp = var(8);
            let actuals = [(x, a), (r, tmp)];
            let writes = [r];
            let call = Stmt::Call { proc_, actuals: &actuals, writes: &writes };
            let copy_back = Stmt::Assign { var: a, expr: tmp };
            let step = Stmt::Assign { var: k, expr: k + 1u32 };
            let loop_body = Stmt::Seq {
                first: &call,
                second: &Stmt::Seq { first: &copy_back, second: &step },
            };
            let inv = smt::and(smt::ule_const(a, 20), smt::ule_const(k, 4));
            let loop_ = Stmt::While {
                cond: smt::ult_const(k, 4),
                invariant: inv,
                variant: Some(smt::sub(smt::word(4, 3), k)),
                body: &loop_body,
            };
            let init_a = Stmt::Assign { var: a, expr: smt::word(0, 8) };
            let init_k = Stmt::Assign { var: k, expr: smt::word(0, 3) };
            let prog = Stmt::Seq {
                first: &init_a,
                second: &Stmt::Seq { first: &init_k, second: &loop_ },
            };
            let report = wp::verify(&prog, smt::truth(true), smt::ule_const(a, 20));
            (report.is_verified(), report.first_failure().map(|(ob, _)| ob.rule))
        };

        let (ok, why) = run(&sat_inc);
        println!("with `r <= 20` in the postcondition : verified = {}", ok);
        if let Some(rule) = why {
            println!("  failed: {:?}", rule);
        }

        let (ok_weak, why_weak) = run(&weak);
        println!("without it                          : verified = {}", ok_weak);
        match why_weak {
            Some(Rule::LoopPreserve) => {
                println!("  failed: LoopPreserve -- and that is the point.");
                println!("  The invariant is preserved only because the callee promises `r <= 20`.");
                println!("  The caller never reads the body, so that bound is the entire reason");
                println!("  the proof goes through. Drop it and the loop stops being provable.");
            }
            Some(rule) => println!("  failed: {:?}", rule),
            None => println!("  unexpectedly verified, which would make the first result weak"),
        }
        println!();
    });

    // ---------------------------------------------------------------------
    // The rules that keep a call honest.
    // ---------------------------------------------------------------------
    println!("=== what a call is not allowed to do ===\n");

    smt::with_fresh(|| {
        let x = var(8);
        let r = var(8);
        let body = Stmt::Assign { var: r, expr: x + x };
        let double = Proc {
            name: "double",
            requires: smt::ule_const(x, 100),
            ensures: smt::eq(r, x + x),
            body: &body,
        };
        let a = var(8);
        let c = var(8);
        let writes = [r];
        let init = Stmt::Assign { var: a, expr: smt::word(5, 8) };

        // 1. A write the caller does not name.
        let missing = [(x, a)];
        let call = Stmt::Call { proc_: &double, actuals: &missing, writes: &writes };
        let prog = Stmt::Seq { first: &init, second: &call };
        let rep = wp::verify(&prog, smt::truth(true), smt::truth(true));
        println!("callee writes `r`, caller never names it:");
        println!(
            "  failed   : {:?}",
            rep.first_failure().map(|(ob, _)| ob.rule)
        );
        println!("             the call is unmodelled, so the caller's state is unknown\n");

        // 2. A write landing on a variable the call also reads.
        let aliased = [(x, a), (r, a)];
        let call = Stmt::Call { proc_: &double, actuals: &aliased, writes: &writes };
        let prog = Stmt::Seq { first: &init, second: &call };
        let rep = wp::verify(&prog, smt::truth(true), smt::truth(true));
        println!("`x -> a, r -> a`, so the write lands on a read variable:");
        println!(
            "  failed   : {:?}",
            rep.first_failure().map(|(ob, _)| ob.rule)
        );
        println!("             otherwise the assumed postcondition would be `a == a + a`,");
        println!("             which silently forces a == 0 and proves anything\n");

        // 3. Two writes onto one variable.
        let two_writes = [r, x];
        println!("two writes onto one variable:");
        println!(
            "  rejected : {}",
            !Stmt::frame(&double, &aliased, &two_writes)
        );
        println!("             an order-dependent assignment is what simultaneity rules out\n");

        // 4. The well-formed call, for contrast.
        let proper = [(x, a), (r, c)];
        println!("the well-formed call x -> a, r -> c:");
        println!("  accepted : {}", Stmt::frame(&double, &proper, &writes));
        println!();
    });

    // ---------------------------------------------------------------------
    // The frame must be complete, not merely well-formed.
    // ---------------------------------------------------------------------
    println!("=== the frame must be complete ===\n");
    println!("A declared frame that *under*-states what a callee writes is not a");
    println!("bookkeeping error, it is unsound: the caller goes on believing a variable");
    println!("that was clobbered. So the declared frame is checked against the frame");
    println!("derived from the body.\n");

    smt::with_fresh(|| {
        let x = var(8);
        let r = var(8);
        let scratch = var(8);
        let a1 = Stmt::Assign { var: scratch, expr: x + x };
        let a2 = Stmt::Assign { var: r, expr: scratch };
        let body = Stmt::Seq { first: &a1, second: &a2 };
        let dbl = Proc {
            name: "dbl",
            requires: smt::truth(true),
            ensures: smt::eq(r, x + x),
            body: &body,
        };
        let a = var(8);
        let c = var(8);
        let s = var(8);
        let actuals = [(x, a), (r, c), (scratch, s)];

        let derived = wp::writes(&body);
        println!("dbl's body writes {} variable(s); derived frame covers `scratch`: {}",
                 derived.len(), derived.contains(&scratch));
        let empty: [discharge::smt::Var; 0] = [];
        println!("declaring an empty frame        : accepted = {}", Stmt::frame(&dbl, &actuals, &empty));
        println!("  -> rejected, so the false proof is unreachable");
        let honest = [r, scratch];
        println!("declaring the truth (r, scratch): accepted = {}", Stmt::frame(&dbl, &actuals, &honest));
        println!("declaring extra (r, scratch, x) : accepted = {}", Stmt::frame(&dbl, &actuals, &[r, scratch, x]));
        println!("  -> over-declaring is fine: the frame rule is conservative\n");
    });

    // ---------------------------------------------------------------------
    // Two-state specifications: a snapshot, not an `old` operator.
    // ---------------------------------------------------------------------
    println!("=== two-state specifications ===\n");
    println!("\"The result equals the argument that came in, plus one\" is a two-state");
    println!("property. It needs no `old` operator: a variable the callee cannot write");
    println!("has the same value before and after, so `old(x)` *is* `x` -- provided the");
    println!("frame is honest. What was missing was a way to ask which variables survive,");
    println!("because the engine was already assuming it silently. `wp::unchanged` answers");
    println!("from the derived frame, so a caller cannot talk it into a wrong answer.\n");

    smt::with_fresh(|| {
        let x = var(8);
        let r = var(8);
        let body = Stmt::Assign { var: r, expr: x + 1u32 };
        let bump = Proc {
            name: "bump",
            requires: smt::ule_const(x, 10),
            ensures: smt::eq(r, x + 1u32),
            body: &body,
        };
        let a = var(8);
        let snapshot = var(8);
        let c = var(8);
        let actuals = [(x, a), (r, c)];
        let declared = [r];
        let call = Stmt::Call { proc_: &bump, actuals: &actuals, writes: &declared };

        println!("bump: requires x <= 10, ensures r == x + 1");
        println!("  unchanged(a)?  {}  <- the argument is read-only", wp::unchanged(&bump, &actuals, a));
        println!("  unchanged(c)?  {}  <- the result is written", wp::unchanged(&bump, &actuals, c));

        // a := 5; old_a := a; c := bump(a); assert c == old_a + 1 && a == old_a
        let init_a = Stmt::Assign { var: a, expr: smt::word(5, 8) };
        let snap = Stmt::Assign { var: snapshot, expr: a };
        let prefix = Stmt::Seq { first: &init_a, second: &snap };
        let prog = Stmt::Seq { first: &prefix, second: &call };
        let post = smt::and(smt::eq(c, snapshot + 1u32), smt::eq(a, snapshot));
        let report = wp::verify(&prog, smt::truth(true), post);
        println!();
        println!("a := 5; old_a := a; c := bump(a)");
        println!("assert c == old_a + 1 && a == old_a");
        println!("  verified : {}", report.is_verified());
        println!("  The snapshot is an ordinary assignment, not new machinery.\n");

        // The control: a written variable's old value is not recoverable.
        let init_c = Stmt::Assign { var: c, expr: smt::word(99, 8) };
        let prog2 = Stmt::Seq {
            first: &init_a,
            second: &Stmt::Seq { first: &init_c, second: &call },
        };
        let rep2 = wp::verify(&prog2, smt::truth(true), smt::eq_const(c, 99));
        println!("the control: c := 99; c := bump(a); assert c == 99");
        println!("  verified : {}  <- correct, the old value is gone", rep2.is_verified());
        println!("  A call *havocs* what it writes: the target is renamed to a fresh");
        println!("  variable, so the pre-call value cannot masquerade as the result.\n");
    });

    // ---------------------------------------------------------------------
    // The sharp edge, stated rather than hidden.
    // ---------------------------------------------------------------------
    println!("=== the sharp edge ===\n");
    println!("`frame` checks the *shape* of the rename, not its meaning. A caller who");
    println!("wires the result onto the wrong variable passes the check and gets a proof");
    println!("about a program it did not write. And a caller that believes a contract whose");
    println!("body never established it verifies anyway, because the caller does not read");
    println!("the body. Both are pinned by tests rather than left to be discovered.\n");
    println!("Which is why the discipline is: verify every body against its contract");
    println!("(`verify_proc`), and trust nothing else.\n");

    let _ = Verdict::Valid;
    println!("done");
}
