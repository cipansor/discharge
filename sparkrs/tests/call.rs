//! Modular verification: procedures verified once, calls reasoned about through
//! contracts.
//!
//! The point of a contract is that the caller does not have to look at the callee's
//! body. These tests check both halves of that: the caller's proof goes through on
//! the contract alone, and it *fails* when the contract is not established or not
//! respected. A modular verifier that only ever says yes would be worthless, so
//! every positive test here has a matching negative one.

use sparkrs::smt::{self, var, Var, Verdict};
use sparkrs::wp::{self, Proc, Rule, Stmt, MAX_CALL_ARGS, MAX_WRITES};

/// `double`: requires `x <= 100`, ensures `r == x + x`.
///
/// Returns the pieces separately because `Proc` borrows the body and the arena is
/// not `Send`; each test builds its own.
fn double_parts() -> (Var, Var, Stmt<'static>) {
    let x = var(8);
    let r = var(8);
    let body = Stmt::Assign { var: r, expr: x + x };
    (x, r, body)
}

#[test]
fn a_procedure_verifies_against_its_own_contract() {
    smt::with_fresh(|| {
        let (x, r, body) = double_parts();
        let p = Proc {
            name: "double",
            requires: smt::ule_const(x, 100),
            ensures: smt::eq(r, x + x),
            body: &body,
        };
        let report = wp::verify_proc(&p);
        assert!(report.is_verified(), "{:?}", report.first_failure());
        // A procedure with no loops has no side obligations; the contract carries
        // the whole proof.
        assert_eq!(report.count, 0);
        // No loops, so nothing can diverge and the report is `Total`. That is the
        // documented meaning: `Total` needs *every* loop to carry a variant, and
        // there are none.
        assert_eq!(report.correctness(), wp::Correctness::Total);
    });
}

#[test]
fn a_call_is_reasoned_about_through_the_contract_alone() {
    smt::with_fresh(|| {
        let (x, r, body) = double_parts();
        let p = Proc {
            name: "double",
            requires: smt::ule_const(x, 100),
            ensures: smt::eq(r, x + x),
            body: &body,
        };

        // Caller: a := 5; c := double(a); assert c == 10
        let a = var(8);
        let c = var(8);
        let actuals = [(x, a), (r, c)];
        let writes = [r];
        let call = Stmt::Call { proc_: &p, actuals: &actuals, writes: &writes };
        let init = Stmt::Assign { var: a, expr: smt::word(5, 8) };
        let prog = Stmt::Seq { first: &init, second: &call };

        let report = wp::verify(&prog, smt::truth(true), smt::eq_const(c, 10));
        assert!(report.is_verified(), "{:?}", report.first_failure());
        // Exactly one obligation: the caller must establish the precondition. The
        // postcondition is *assumed*, so it costs nothing.
        assert_eq!(report.count, 1);
        assert_eq!(report.obligations[0].unwrap().rule, Rule::CallRequires);
    });

    // Execution: the same computation in Rust, for every input in range.
    for v in [0u8, 1, 5, 50, 100] {
        assert_eq!(v.wrapping_add(v), v * 2);
    }
}

#[test]
fn a_caller_that_breaks_the_precondition_is_caught() {
    smt::with_fresh(|| {
        let (x, r, body) = double_parts();
        let p = Proc {
            name: "double",
            requires: smt::ule_const(x, 100),
            ensures: smt::eq(r, x + x),
            body: &body,
        };

        let a = var(8);
        let c = var(8);
        let actuals = [(x, a), (r, c)];
        let writes = [r];
        let call = Stmt::Call { proc_: &p, actuals: &actuals, writes: &writes };
        // 200 > 100, so the precondition does not hold.
        let init = Stmt::Assign { var: a, expr: smt::word(200, 8) };
        let prog = Stmt::Seq { first: &init, second: &call };

        let report = wp::verify(&prog, smt::truth(true), smt::eq_const(c, 10));
        let (ob, _) = report.first_failure().expect("200 is out of range");
        assert_eq!(
            ob.rule,
            Rule::CallRequires,
            "the fault is the caller's, not the callee's"
        );
    });
}

#[test]
fn an_unmodelled_call_is_reported_rather_than_assumed() {
    // The callee writes `r`, but the caller never names it, so there is nowhere for
    // that write to land. The call is unmodelled: the caller's state afterwards is
    // unknown, and no proof can be built on it.
    smt::with_fresh(|| {
        let (x, r, body) = double_parts();
        let p = Proc {
            name: "double",
            requires: smt::ule_const(x, 100),
            ensures: smt::eq(r, x + x),
            body: &body,
        };

        let a = var(8);
        let actuals = [(x, a)]; // `r` missing
        let writes = [r];
        let call = Stmt::Call { proc_: &p, actuals: &actuals, writes: &writes };
        let init = Stmt::Assign { var: a, expr: smt::word(5, 8) };
        let prog = Stmt::Seq { first: &init, second: &call };

        let report = wp::verify(&prog, smt::truth(true), smt::truth(true));
        let (ob, _) = report
            .first_failure()
            .expect("an unframed call cannot be assumed away");
        assert_eq!(ob.rule, Rule::CallFrame);
        // And it is a reported obligation, not a panic: the whole program can be
        // checked in one run.
    });
}

#[test]
fn a_rename_that_is_not_a_function_is_rejected() {
    // Two globals renamed onto the same local is not a rename at all. Accepting it
    // would make the substitution depend on which pair was seen last.
    smt::with_fresh(|| {
        let (x, r, body) = double_parts();
        let p = Proc {
            name: "double",
            requires: smt::ule_const(x, 100),
            ensures: smt::eq(r, x + x),
            body: &body,
        };
        let a = var(8);
        // `x -> a, r -> a`: the write to `r` lands on `a`, which the call also
        // reads. `ensures` would be assumed as `a == a + a`, silently forcing
        // `a == 0` and letting the engine prove anything about it. Rejected.
        let aliased = [(x, a), (r, a)];
        let writes = [r];
        assert!(
            !Stmt::frame(&p, &aliased, &writes),
            "a write landing on a read variable must not be accepted"
        );

        // Two writes onto one variable is an order-dependent assignment. Rejected.
        let two_writes = [r, x];
        assert!(
            !Stmt::frame(&p, &aliased, &two_writes),
            "two writes onto one variable must not be accepted"
        );

        // A repeated global is not a rename. Rejected.
        let c = var(8);
        let repeated = [(x, a), (x, c), (r, c)];
        assert!(
            !Stmt::frame(&p, &repeated, &writes),
            "a repeated global must not be accepted"
        );

        // The well-formed version is accepted.
        let proper = [(x, a), (r, c)];
        assert!(Stmt::frame(&p, &proper, &writes));
    });
}

#[test]
fn the_frame_check_is_about_shape_only() {
    // Worth pinning, because it is the sharp edge of this design: `frame` asks
    // whether the write is *expressible*, not whether it is *right*. Renaming the
    // result onto the wrong caller variable passes the check. The caller gets a
    // proof about a program it did not write.
    smt::with_fresh(|| {
        let (x, r, body) = double_parts();
        let p = Proc {
            name: "double",
            requires: smt::ule_const(x, 100),
            ensures: smt::eq(r, x + x),
            body: &body,
        };
        let a = var(8);
        let wrong = var(8);
        let right = var(8);
        let writes = [r];
        // `r` is mapped to `wrong`, which satisfies the shape check.
        let actuals = [(x, a), (r, wrong)];
        assert!(Stmt::frame(&p, &actuals, &writes));

        // So a caller that then reasons about `right` proves nothing, and the
        // engine correctly refuses to prove it.
        let call = Stmt::Call { proc_: &p, actuals: &actuals, writes: &writes };
        let init = Stmt::Assign { var: a, expr: smt::word(5, 8) };
        let prog = Stmt::Seq { first: &init, second: &call };
        let report = wp::verify(&prog, smt::truth(true), smt::eq_const(right, 10));
        assert!(
            !report.is_verified(),
            "the engine must not pretend the write landed on `right`"
        );
    });
}

#[test]
fn the_caller_depends_on_the_contract_not_the_body() {
    // The heart of modularity, and also its danger. If the contract is wrong, the
    // caller's proof still goes through -- because the caller never looks at the
    // body. That is why every procedure's body has to be verified too, and the
    // test below shows both halves.
    smt::with_fresh(|| {
        let (x, r, body) = double_parts();
        // A contract that claims the result is always 42. The body does not
        // establish it, so `verify_proc` must fail...
        let lie = Proc {
            name: "double",
            requires: smt::ule_const(x, 100),
            ensures: smt::eq_const(r, 42),
            body: &body,
        };
        let callee = wp::verify_proc(&lie);
        assert!(!callee.is_verified(), "the body does not imply r == 42");
        assert_eq!(callee.contract.rule, Rule::Body);

        // ...yet a caller that believes the contract verifies anyway. That is not a
        // bug in the caller's rule; it is the reason the callee's obligation exists.
        let a = var(8);
        let c = var(8);
        let actuals = [(x, a), (r, c)];
        let writes = [r];
        let call = Stmt::Call { proc_: &lie, actuals: &actuals, writes: &writes };
        let init = Stmt::Assign { var: a, expr: smt::word(5, 8) };
        let prog = Stmt::Seq { first: &init, second: &call };
        let caller = wp::verify(&prog, smt::truth(true), smt::eq_const(c, 42));
        assert!(
            caller.is_verified(),
            "the caller's proof rests on the contract, which is the point"
        );
    });
}

#[test]
fn a_call_inside_a_loop_body_verifies() {
    // The case that needs a call to compose with the loop rules rather than only
    // with straight-line code:
    //
    //   sat_inc: requires x <= 20, ensures r <= 20 && (x < 20 => r == x + 1)
    //            body: r := if x < 20 { x + 1 } else { 20 }
    //
    //   a := 0
    //   for k := 0; k < 4; k += 1 { tmp := sat_inc(a); a := tmp }
    //   assert a <= 20
    //
    // The invariant is `a <= 20 && k <= 4`, and the `a <= 20` half is preserved
    // *only* because the callee's postcondition says `r <= 20`. The caller never
    // looks at the body, so that bound is the whole reason the proof goes through.
    // `dropping_the_bound_from_the_postcondition_breaks_the_loop` is the control.
    //
    // My first attempt at this test used a plain `r == x + 1` increment with
    // invariant `a <= 19`, and the engine produced a counterexample at `a == 19`:
    // the invariant was simply not preserved, and it was my invariant that was
    // wrong, not the rule.
    //
    // The result goes to a temporary and is then copied back. Writing straight into
    // `a` would alias a read and the frame check rejects it.
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
        // The callee verifies on its own first, or the assumption would be a lie.
        let callee = wp::verify_proc(&sat_inc);
        assert!(callee.is_verified(), "{:?}", callee.first_failure());

        let a = var(8);
        let k = var(3);
        let tmp = var(8);
        let actuals = [(x, a), (r, tmp)];
        let writes = [r];
        let call = Stmt::Call { proc_: &sat_inc, actuals: &actuals, writes: &writes };
        let copy_back = Stmt::Assign { var: a, expr: tmp };
        let step = Stmt::Assign { var: k, expr: k + 1u32 };
        let loop_body = Stmt::Seq {
            first: &call,
            second: &Stmt::Seq {
                first: &copy_back,
                second: &step,
            },
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
        assert!(report.is_verified(), "{:?}", report.first_failure());
        assert!(report.has_termination_proof());

        // The call obligation is present and attributed to the caller.
        let call_obs: Vec<_> = report
            .obligations
            .iter()
            .flatten()
            .filter(|ob| ob.rule == Rule::CallRequires)
            .collect();
        assert_eq!(call_obs.len(), 1);
        assert_eq!(call_obs[0].discharge(), Verdict::Valid);
    });

    // Execution: four saturating increments from zero stay within the bound, and
    // the saturated case stays at the bound.
    let sat_inc = |v: u8| if v < 20 { v + 1 } else { 20 };
    let mut a = 0u8;
    for _ in 0..4 {
        a = sat_inc(a);
    }
    assert_eq!(a, 4);
    assert!(a <= 20);
    assert_eq!(sat_inc(20), 20);
    assert_eq!(sat_inc(255), 20);
}

#[test]
fn dropping_the_bound_from_the_postcondition_breaks_the_loop() {
    // The control for the test above. With `ensures` reduced to
    // `x < 20 => r == x + 1`, the callee still verifies, but the loop invariant is
    // no longer preserved: the assumed postcondition no longer bounds the result.
    // If this test passed, the previous one would not be evidence that the
    // postcondition is actually being used.
    smt::with_fresh(|| {
        let x = var(8);
        let r = var(8);
        let body = Stmt::Assign {
            var: r,
            expr: smt::ite(x.lt_val(20), x + 1u32, smt::word(20, 8)),
        };
        let weak = Proc {
            name: "sat_inc_weak",
            requires: smt::ule_const(x, 20),
            ensures: smt::implies(x.lt_val(20), smt::eq(r, x + 1u32)),
            body: &body,
        };
        assert!(wp::verify_proc(&weak).is_verified());

        let a = var(8);
        let k = var(3);
        let tmp = var(8);
        let actuals = [(x, a), (r, tmp)];
        let writes = [r];
        let call = Stmt::Call { proc_: &weak, actuals: &actuals, writes: &writes };
        let copy_back = Stmt::Assign { var: a, expr: tmp };
        let step = Stmt::Assign { var: k, expr: k + 1u32 };
        let loop_body = Stmt::Seq {
            first: &call,
            second: &Stmt::Seq {
                first: &copy_back,
                second: &step,
            },
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
        let (ob, _) = report
            .first_failure()
            .expect("without `r <= 20` the invariant cannot be preserved");
        assert_eq!(ob.rule, Rule::LoopPreserve);
    });
}

#[test]
fn verify_proc_and_verify_agree() {
    // A procedure is a body with a contract, so the two entry points must be the
    // same computation. If they ever diverge, one of them is lying.
    smt::with_fresh(|| {
        let (x, r, body) = double_parts();
        let p = Proc {
            name: "double",
            requires: smt::ule_const(x, 100),
            ensures: smt::eq(r, x + x),
            body: &body,
        };
        let via_proc = wp::verify_proc(&p);
        let via_verify = wp::verify(&body, smt::ule_const(x, 100), smt::eq(r, x + x));
        assert_eq!(via_proc.is_verified(), via_verify.is_verified());
        assert_eq!(via_proc.count, via_verify.count);
        assert_eq!(
            via_proc.contract.discharge(),
            via_verify.contract.discharge()
        );
    });
}

#[test]
fn a_swapped_argument_order_is_caught_by_the_precondition() {
    // `inc`: requires `x <= 10`, ensures `r == x + 1`. Called with the *result*
    // wired to the input by mistake: the precondition then has to hold of the
    // result variable, which nothing constrains, so the proof must fail.
    smt::with_fresh(|| {
        let x = var(8);
        let r = var(8);
        let body = Stmt::Assign { var: r, expr: x + 1u32 };
        let inc = Proc {
            name: "inc",
            requires: smt::ule_const(x, 10),
            ensures: smt::eq(r, x + 1u32),
            body: &body,
        };

        let a = var(8);
        let c = var(8);
        // Correct wiring verifies.
        let good = [(x, a), (r, c)];
        let writes = [r];
        let call = Stmt::Call { proc_: &inc, actuals: &good, writes: &writes };
        let init = Stmt::Assign { var: a, expr: smt::word(3, 8) };
        let prog = Stmt::Seq { first: &init, second: &call };
        assert!(wp::verify(&prog, smt::truth(true), smt::eq_const(c, 4)).is_verified());

        // Swapped: `a` receives the result and `c` is the input. Nothing bounds
        // `c`, so the precondition is not established.
        let swapped = [(x, c), (r, a)];
        let bad = Stmt::Call { proc_: &inc, actuals: &swapped, writes: &writes };
        let prog2 = Stmt::Seq { first: &init, second: &bad };
        let report = wp::verify(&prog2, smt::truth(true), smt::truth(true));
        let (ob, _) = report.first_failure().expect("the input is unbounded");
        assert_eq!(ob.rule, Rule::CallRequires);
    });
}

// ---------------------------------------------------------------------------
// The frame must be complete, not merely well-formed.
// ---------------------------------------------------------------------------

#[test]
fn under_declaring_the_frame_is_rejected() {
    // The soundness hole, found by probing rather than by reasoning.
    //
    // `dbl` writes both `r` and a helper `scratch`. A caller that declares an empty
    // frame is claiming `scratch` survived the call. The engine used to accept that
    // and then *prove* `s == 7` after the call — while the callee had overwritten
    // `s` with `a + a`. A proof about a program that does not exist is worse than no
    // proof, so the declared frame is now checked against the frame derived from the
    // body.
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
        assert!(wp::verify_proc(&dbl).is_verified());

        // The derived frame really does include `scratch`.
        let derived = wp::writes(&body);
        assert!(derived.contains(&scratch));
        assert!(derived.contains(&r));

        let a = var(8);
        let c = var(8);
        let s = var(8);
        let actuals = [(x, a), (r, c), (scratch, s)];

        // An empty frame is a lie and must be rejected.
        let empty: [Var; 0] = [];
        assert!(
            !Stmt::frame(&dbl, &actuals, &empty),
            "an empty frame cannot be declared for a body that writes"
        );

        // And the false proof must be gone. Declaring the empty frame and asserting
        // that `s` survived now fails with CallFrame rather than verifying.
        let call = Stmt::Call { proc_: &dbl, actuals: &actuals, writes: &empty };
        let init = Stmt::Assign { var: s, expr: smt::word(7, 8) };
        let prog = Stmt::Seq { first: &init, second: &call };
        let report = wp::verify(&prog, smt::truth(true), smt::eq_const(s, 7));
        let (ob, _) = report
            .first_failure()
            .expect("the under-declared frame must not verify");
        assert_eq!(ob.rule, Rule::CallFrame);

        // Declaring the truth is accepted.
        let honest = [r, scratch];
        assert!(Stmt::frame(&dbl, &actuals, &honest));

        // And over-declaring is fine: the frame rule is conservative.
        let generous = [r, scratch, x];
        assert!(Stmt::frame(&dbl, &actuals, &generous));
    });
}

#[test]
fn the_derived_frame_covers_branches_and_loops() {
    // A write inside a branch or a loop still counts, because "may write" is what
    // matters: the caller cannot know which path the callee took. If the derivation
    // missed these, a callee could hide a write from its own frame check.
    smt::with_fresh(|| {
        let x = var(8);
        let y = var(8);
        let z = var(8);
        let w = var(8);

        // if x < 10 { y := 1 } else { z := 2 }
        let then_ = Stmt::Assign { var: y, expr: smt::word(1, 8) };
        let else_ = Stmt::Assign { var: z, expr: smt::word(2, 8) };
        let branch = Stmt::If {
            cond: smt::ult_const(x, 10),
            then_: &then_,
            else_: &else_,
        };
        let found = wp::writes(&branch);
        assert!(found.contains(&y));
        assert!(found.contains(&z));
        assert!(!found.contains(&x));

        // while x < 10 { w := w + 1 }
        let step = Stmt::Assign { var: w, expr: w + 1u32 };
        let loop_ = Stmt::While {
            cond: smt::ult_const(x, 10),
            invariant: smt::truth(true),
            variant: None,
            body: &step,
        };
        let found = wp::writes(&loop_);
        assert!(found.contains(&w));

        // A simultaneous assignment contributes every target.
        let binds = [(y, z), (w, x)];
        let many = Stmt::AssignMany { binds: &binds };
        let found = wp::writes(&many);
        assert!(found.contains(&y));
        assert!(found.contains(&w));

        // `assume` and `assert` write nothing.
        assert!(wp::writes(&Stmt::Assert(smt::truth(true))).is_empty());
        assert!(wp::writes(&Stmt::Skip).is_empty());
    });
}

#[test]
fn a_nested_call_contributes_its_callees_writes() {
    // If `outer` calls `inner`, then `outer`'s derived frame must include whatever
    // `inner` writes, mapped through `outer`'s actuals. Otherwise a caller of `outer`
    // could under-declare and reintroduce the hole one level up.
    smt::with_fresh(|| {
        let ix = var(8);
        let ir = var(8);
        let inner_body = Stmt::Assign { var: ir, expr: ix + 1u32 };
        let inner = Proc {
            name: "inner",
            requires: smt::truth(true),
            ensures: smt::eq(ir, ix + 1u32),
            body: &inner_body,
        };

        let ox = var(8);
        let or_ = var(8);
        let actuals = [(ix, ox), (ir, or_)];
        let writes_inner = [ir];
        let call = Stmt::Call {
            proc_: &inner,
            actuals: &actuals,
            writes: &writes_inner,
        };
        let outer_body = Stmt::Seq {
            first: &call,
            second: &Stmt::Skip,
        };

        // `outer` writes `or_`, because that is where `inner`'s `ir` lands.
        let found = wp::writes(&outer_body);
        assert!(found.contains(&or_), "the nested write must propagate");
        assert!(!found.contains(&ir), "the callee's own name must not leak");

        // Now `outer` in turn is called. Its own actuals map `ox` and `or_` to the
        // caller's variables, and its declared frame must cover the write that was
        // propagated from `inner`.
        let outer = Proc {
            name: "outer",
            requires: smt::truth(true),
            ensures: smt::eq(or_, ox + 1u32),
            body: &outer_body,
        };
        let gx = var(8);
        let gh = var(8);
        let outer_actuals = [(ox, gx), (or_, gh)];
        let empty: [Var; 0] = [];
        assert!(
            !Stmt::frame(&outer, &outer_actuals, &empty),
            "the propagated write must also be declared one level up"
        );
        // Declaring the propagated write is accepted.
        assert!(Stmt::frame(&outer, &outer_actuals, &[or_]));
    });
}

#[test]
fn a_callee_that_writes_nothing_needs_no_frame() {
    // The other end of the range: a pure procedure has an empty derived frame, so a
    // caller declaring nothing is correct rather than merely tolerated.
    smt::with_fresh(|| {
        let x = var(8);
        let r = var(8);
        // The body writes `r`, so to get a genuinely empty frame the procedure must
        // write nothing at all -- a predicate rather than a function.
        let pure_body = Stmt::Skip;
        let is_small = Proc {
            name: "is_small",
            requires: smt::truth(true),
            ensures: smt::ult_const(x, 10),
            body: &pure_body,
        };
        assert!(wp::writes(&pure_body).is_empty());
        let a = var(8);
        let actuals = [(x, a)];
        let empty: [Var; 0] = [];
        assert!(Stmt::frame(&is_small, &actuals, &empty));
        let _ = r;
    });
}

// ---------------------------------------------------------------------------
// Two-state specifications.
// ---------------------------------------------------------------------------

#[test]
fn two_state_specs_via_a_caller_snapshot() {
    // "The result equals the argument that came in, plus one" is a two-state
    // property, and it needs a snapshot — but not a general `old` operator.
    //
    // `bump` writes `r` and reads `x`. If the caller captures `x`'s value into a
    // temporary *before* the call, then after the call that temporary still holds the
    // entry value, because the callee cannot write it (the derived frame says so).
    // `old(x)` and the snapshot are therefore the same thing, and the snapshot needs
    // no new machinery: it is an ordinary assignment.
    //
    //   bump: requires x <= 10, ensures r == x + 1
    //   a := 5; old_a := a; c := bump(a); assert c == old_a + 1 && a == old_a
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
        assert!(wp::verify_proc(&bump).is_verified());

        let a = var(8);
        let snapshot = var(8);
        let c = var(8);
        let actuals = [(x, a), (r, c)];
        let declared = [r];
        let call = Stmt::Call { proc_: &bump, actuals: &actuals, writes: &declared };

        // The query, before doing anything: which caller variables survive?
        let mut buf = [Var::SENTINEL; wp::MAX_CALL_ARGS];
        let survive = wp::unchanged_vars(&bump, &actuals, &mut buf);
        assert!(survive.contains(&a), "the argument is read-only, so it survives");
        assert!(!survive.contains(&c), "the result is written, so it does not");
        assert!(wp::unchanged(&bump, &actuals, a));
        assert!(!wp::unchanged(&bump, &actuals, c));
        // A variable the call never names is also untouched.
        let unrelated = var(8);
        assert!(wp::unchanged(&bump, &actuals, unrelated));

        let init_a = Stmt::Assign { var: a, expr: smt::word(5, 8) };
        let snap = Stmt::Assign { var: snapshot, expr: a };
        let prefix = Stmt::Seq { first: &init_a, second: &snap };
        let prog = Stmt::Seq { first: &prefix, second: &call };

        // The two-state postcondition: the result follows the entry value, and the
        // argument itself is unchanged across the call.
        let post = smt::and(
            smt::eq(c, snapshot + 1u32),
            smt::eq(a, snapshot),
        );
        let report = wp::verify(&prog, smt::truth(true), post);
        assert!(report.is_verified(), "{:?}", report.first_failure());
    });

    // Execution: the snapshot really does hold the entry value.
    let a = 5u8;
    let snapshot = a;
    let c = a + 1;
    assert_eq!(c, snapshot + 1);
    assert_eq!(a, snapshot);
}

#[test]
fn the_snapshot_discipline_is_needed_for_written_variables() {
    // The control for the test above, and the reason a snapshot is a *discipline*
    // rather than a convenience: for a variable the callee writes, there is no query
    // that helps. `c` is written, so a postcondition mentioning `c`'s old value is
    // simply false — the old value is gone.
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
        let c = var(8);
        let actuals = [(x, a), (r, c)];
        let declared = [r];
        let call = Stmt::Call { proc_: &bump, actuals: &actuals, writes: &declared };
        let init_a = Stmt::Assign { var: a, expr: smt::word(5, 8) };
        let init_c = Stmt::Assign { var: c, expr: smt::word(99, 8) };
        let prog = Stmt::Seq {
            first: &init_a,
            second: &Stmt::Seq { first: &init_c, second: &call },
        };
        // "c still holds what it held before the call" is false, and the engine says
        // so rather than quietly accepting it.
        let report = wp::verify(&prog, smt::truth(true), smt::eq_const(c, 99));
        assert!(
            !report.is_verified(),
            "a written variable's old value is not recoverable"
        );
        // The query agrees: `c` does not survive.
        assert!(!wp::unchanged(&bump, &actuals, c));
    });
}

#[test]
fn an_unchanged_query_cannot_be_talked_into_a_wrong_answer() {
    // The query reads the *derived* frame, so the declared frame cannot corrupt it.
    // Here the caller declares an empty frame for a callee that writes `r`; the
    // declaration is refused by `frame`, and the query still reports the truth.
    smt::with_fresh(|| {
        let x = var(8);
        let r = var(8);
        let body = Stmt::Assign { var: r, expr: x + x };
        let dbl = Proc {
            name: "dbl",
            requires: smt::truth(true),
            ensures: smt::eq(r, x + x),
            body: &body,
        };
        let a = var(8);
        let c = var(8);
        let actuals = [(x, a), (r, c)];
        let lie: [Var; 0] = [];
        assert!(!Stmt::frame(&dbl, &actuals, &lie));
        // Even so, the query answers from the body and says `c` is written.
        assert!(!wp::unchanged(&dbl, &actuals, c));
        assert!(wp::unchanged(&dbl, &actuals, a));
    });
}

#[test]
fn an_over_long_body_is_unmodelled_not_partially_modelled() {
    // The fourth soundness hole, and the one that defeated the fix for the first.
    //
    // `writes` used to return `(array, count)` and truncate at `MAX_WRITES`, silently.
    // The frame-completeness check I added for the under-declared-frame hole then
    // compared the declared frame against a *prefix* of the truth, so a callee writing
    // more than `MAX_WRITES` variables looked like one writing exactly `MAX_WRITES` — and
    // a caller could "prove" that a variable survived a call that clobbered it.
    //
    // The probe printed `caller proved 'victim == 9' : true` for a callee that assigns
    // `victim := x + x`. A truncated frame is therefore not a smaller frame; it is an
    // unknown frame, and the only sound answer is to refuse the call.
    smt::with_fresh(|| {
        let x = var(8);
        let r = var(8);
        // 16 helper variables plus the result: 17 writes, one past the cap.
        let helpers: Vec<Var> = (0..MAX_WRITES).map(|_| var(8)).collect();

        let mut nodes: Vec<Stmt> = vec![Stmt::Assign { var: r, expr: x + 1u32 }];
        for h in &helpers {
            nodes.push(Stmt::Assign { var: *h, expr: x + x });
        }
        let mut body = nodes.pop().unwrap();
        while let Some(nd) = nodes.pop() {
            body = Stmt::Seq {
                first: Box::leak(Box::new(nd)),
                second: Box::leak(Box::new(body)),
            };
        }
        let body: &'static Stmt<'static> = Box::leak(Box::new(body));

        // The derived frame must admit it is not the truth.
        let derived = wp::writes(body);
        assert_eq!(derived.len(), MAX_WRITES, "the buffer fills");
        assert!(
            !derived.complete(),
            "a body writing more than MAX_WRITES variables must report incompleteness, \
             not a truncated set"
        );

        let callee = Proc {
            name: "wide",
            requires: smt::truth(true),
            ensures: smt::truth(true),
            body,
        };

        // The caller names every write, so nothing else can reject the call.
        let ca = var(8);
        let ct = var(8);
        let c_helpers: Vec<Var> = (0..MAX_WRITES).map(|_| var(8)).collect();
        let mut actuals: Vec<(Var, Var)> = vec![(x, ca), (r, ct)];
        for (h, c) in helpers.iter().zip(c_helpers.iter()) {
            actuals.push((*h, *c));
        }
        let mut declared: Vec<Var> = vec![r];
        declared.extend(helpers.iter().copied());

        assert!(
            !Stmt::frame(&callee, &actuals, &declared),
            "an over-long body is unmodelled, so the frame must be refused"
        );

        // The victim is the 17th write, the one past the cap. The callee clobbers it.
        let victim = c_helpers[MAX_WRITES - 1];
        assert!(
            !wp::unchanged(&callee, &actuals, victim),
            "`unchanged` must not claim a variable survives a body it cannot fully see"
        );

        let mut out = [Var::SENTINEL; MAX_CALL_ARGS];
        assert!(
            wp::unchanged_vars(&callee, &actuals, &mut out).is_empty(),
            "no variable is known to survive an unmodelled call"
        );

        // And the false proof is unreachable: the call is rejected, so the caller's
        // `victim == 9` cannot be established.
        let init = Stmt::Assign { var: victim, expr: smt::word(9, 8) };
        let call = Stmt::Call {
            proc_: &callee,
            actuals: &actuals,
            writes: &declared,
        };
        let prog = Stmt::Seq { first: &init, second: &call };
        let report = wp::verify(&prog, smt::truth(true), smt::eq_const(victim, 9));
        assert!(
            !report.is_verified(),
            "the caller must not be able to prove a variable survived a call that writes it"
        );
        let (ob, _) = report.first_failure().expect("the call is unmodelled");
        assert_eq!(ob.rule, Rule::CallFrame);
    });
}

#[test]
fn a_body_at_exactly_the_cap_is_still_modelled() {
    // The boundary from the other side: incompleteness must mean "more than the cap",
    // not "the cap", or every wide-but-legal procedure would become unverifiable.
    smt::with_fresh(|| {
        let x = var(8);
        let targets: Vec<Var> = (0..MAX_WRITES).map(|_| var(8)).collect();
        let mut nodes: Vec<Stmt> = targets
            .iter()
            .map(|t| Stmt::Assign { var: *t, expr: x + 1u32 })
            .collect();
        let mut body = nodes.pop().unwrap();
        while let Some(nd) = nodes.pop() {
            body = Stmt::Seq {
                first: Box::leak(Box::new(nd)),
                second: Box::leak(Box::new(body)),
            };
        }
        let body: &'static Stmt<'static> = Box::leak(Box::new(body));

        let derived = wp::writes(body);
        assert_eq!(derived.len(), MAX_WRITES);
        assert!(
            derived.complete(),
            "exactly MAX_WRITES writes is the whole truth, not a truncation"
        );

        let callee = Proc {
            name: "at_cap",
            requires: smt::truth(true),
            ensures: smt::truth(true),
            body,
        };
        let cx = var(8);
        let mut actuals: Vec<(Var, Var)> = vec![(x, cx)];
        let caller_targets: Vec<Var> = (0..MAX_WRITES).map(|_| var(8)).collect();
        for (g, c) in targets.iter().zip(caller_targets.iter()) {
            actuals.push((*g, *c));
        }
        let declared: Vec<Var> = targets.clone();
        assert!(
            Stmt::frame(&callee, &actuals, &declared),
            "a body writing exactly MAX_WRITES variables is modelled"
        );
    });
}

// ---------------------------------------------------------------------------
// `wp::wp` must apply the same call rule as `verify`.
//
// `collect` (which `verify` runs) checks `Stmt::frame` at a call and reports a bad frame
// as an obligation. `wp::wp` is also public and is the rule a caller uses to build a
// weakest precondition by hand, and it did *not* check the frame: it assumed every caller
// variable the callee writes kept its old value. A callee that zeroes `g`, called with an
// empty declared frame, then let `wp(call, g == 7)` come out provable from `g == 7` -- a
// proof that the callee's write did not happen. The honest weakest precondition of an
// unmodelled call is `false`: nothing is guaranteed about the state after it.
// ---------------------------------------------------------------------------

#[test]
fn a_declared_frame_longer_than_the_cap_is_refused() {
    // The open thread after the `writes` truncation fix: `havoc_writes` renames the
    // written targets into a `MAX_CALL_ARGS` buffer and, like the old `writes`, stops at
    // the cap. If a call with more than `MAX_CALL_ARGS` declared writes ever reached it,
    // the writes past the cap would keep their pre-call names, so a claim that one of them
    // changed would be checked against its *old* value -- the exact confusion the havoc
    // exists to prevent.
    //
    // `Stmt::frame` check 3 is what makes that unreachable: it refuses the frame when the
    // number of distinct written targets exceeds `MAX_CALL_ARGS`, before any havoc runs.
    // This test pins that refusal so a future edit that loosens check 3 cannot quietly
    // reintroduce the truncation.
    //
    // The body writes a *single* variable on purpose. With a body at the `MAX_WRITES` cap
    // the derived frame would be complete and the over-long *declared* frame would be
    // caught by check 0 instead, so the test would pass for the wrong reason and would not
    // fail if check 3 were removed -- which is exactly what happened to the first version
    // of this test. Here the derived frame is complete, every declared write has a target,
    // the globals and images are distinct, so checks 0-2 all pass and only the `n_written`
    // cap in check 3 can be what refuses it.
    smt::with_fresh(|| {
        let x = var(8);
        let r = var(8);
        let body: &'static Stmt<'static> =
            Box::leak(Box::new(Stmt::Assign { var: r, expr: x + 1u32 }));
        let callee = Proc {
            name: "one",
            requires: smt::truth(true),
            ensures: smt::truth(true),
            body,
        };
        // `r` plus `MAX_CALL_ARGS` extras: `MAX_CALL_ARGS + 1` declared writes.
        let extra: Vec<Var> = (0..MAX_CALL_ARGS).map(|_| var(8)).collect();
        let cx = var(8);
        let cr = var(8);
        let mut actuals: Vec<(Var, Var)> = vec![(x, cx), (r, cr)];
        let mut declared: Vec<Var> = vec![r];
        for e in &extra {
            actuals.push((*e, var(8)));
            declared.push(*e);
        }
        assert!(wp::writes(body).complete(), "the body's own frame is small and complete");
        assert!(
            !Stmt::frame(&callee, &actuals, &declared),
            "a declared frame of {} writes exceeds the {}-entry havoc buffer and must be \
             refused, not silently truncated",
            declared.len(),
            MAX_CALL_ARGS
        );

        // The boundary: exactly `MAX_CALL_ARGS` declared writes is modelled. The same
        // body, `r` plus `MAX_CALL_ARGS - 1` extras.
        let mut actuals: Vec<(Var, Var)> = vec![(x, cx), (r, cr)];
        let mut declared: Vec<Var> = vec![r];
        for e in extra.iter().take(MAX_CALL_ARGS - 1) {
            actuals.push((*e, var(8)));
            declared.push(*e);
        }
        assert_eq!(declared.len(), MAX_CALL_ARGS);
        assert!(
            Stmt::frame(&callee, &actuals, &declared),
            "a declared frame of exactly MAX_CALL_ARGS writes is modelled"
        );
    });
}

#[test]
fn wp_refuses_to_reason_about_a_call_with_a_bad_frame() {
    smt::with_fresh(|| {
        let g = var(8);
        // The body writes `g`; the declared frame is empty, so the call is unmodelled.
        let body = Stmt::Assign { var: g, expr: smt::word(0, 8) };
        let callee = Proc {
            name: "zero_g",
            requires: smt::truth(true),
            ensures: smt::truth(true),
            body: &body,
        };
        let call = Stmt::Call { proc_: &callee, actuals: &[(g, g)], writes: &[] };

        // The false claim: starting from `g == 7`, the call leaves `g == 7`. With an
        // empty declared frame the old rule havocs nothing, so `wp` was just the
        // postcondition and `pre => wp` came out `Valid` -- a proof that the callee's
        // write to `g` did not happen.
        let pre = g.eq_val(7);
        let w = wp::wp(pre, &call);
        assert!(
            !smt::prove_implies(pre, w).is_proved(),
            "wp trusted an unmodelled call and proved a variable survived a write"
        );
        // And `verify` agrees, for the same program.
        assert!(!wp::verify(&call, pre, pre).is_verified());
    });
}

#[test]
fn wp_still_reasons_about_a_call_with_a_good_frame() {
    smt::with_fresh(|| {
        let x = var(8);
        let r = var(8);
        let body = Stmt::Assign { var: r, expr: x + x };
        let callee = Proc {
            name: "double",
            requires: smt::ule_const(x, 100),
            ensures: smt::eq(r, x + x),
            body: &body,
        };
        let a = var(8);
        let c = var(8);
        let call = Stmt::Call { proc_: &callee, actuals: &[(x, a), (r, c)], writes: &[r] };

        // A well-framed call still yields a usable rule: with the callee's contract
        // assumed, `c == 10` follows from `a == 5`.
        let pre = smt::eq_const(a, 5);
        let goal = smt::implies(pre, wp::wp(c.eq_val(10), &call));
        assert_eq!(smt::prove(goal), Verdict::Valid, "a framed call must still verify");
    });
}

#[test]
fn an_assertion_after_a_call_sees_the_call() {
    // The call analogue of `an_assertion_after_an_if_sees_the_if`, and the third construct
    // to have the same hole: a claim to the *right* of a call was checked in the pre-call
    // state. `a := 5; c := double(a); assert c == 10` was reported as a failure, with the
    // written target `c` free, even though the callee's own contract guarantees `c == 10`.
    //
    // Two halves are needed here, unlike `if` and `while`: the goal must be checked under
    // the call's `ensures`, *and* the written targets must be havoced in the goal as well
    // as in the assumption, because the call renames them. Wrapping without havocing leaves
    // the goal mentioning the old `c`, which proves nothing.
    smt::with_fresh(|| {
        let (x, r, body) = double_parts();
        let p = Proc {
            name: "double",
            requires: smt::ule_const(x, 100),
            ensures: smt::eq(r, x + x),
            body: &body,
        };
        let a = var(8);
        let c = var(8);
        let call = Stmt::Call { proc_: &p, actuals: &[(x, a), (r, c)], writes: &[r] };
        let init = Stmt::Assign { var: a, expr: smt::word(5, 8) };

        // True claim: the contract gives `c == a + a == 10`.
        let s = Stmt::Seq {
            first: &init,
            second: &Stmt::Seq {
                first: &call,
                second: &Stmt::Assert(smt::eq(c, smt::word(10, 8))),
            },
        };
        let r = wp::verify(&s, smt::truth(true), smt::truth(true));
        assert!(
            r.is_verified(),
            "the call's ensures must reach the assertion after it; got {:?}",
            r.first_failure()
        );

        // Teeth: a claim the contract does not establish must still fail.
        let s = Stmt::Seq {
            first: &init,
            second: &Stmt::Seq {
                first: &call,
                second: &Stmt::Assert(smt::eq(c, smt::word(11, 8))),
            },
        };
        let r = wp::verify(&s, smt::truth(true), smt::truth(true));
        assert!(!r.is_verified(), "c == a + a == 10, so c == 11 must fail");

        // Teeth for the havoc: `c := 99` before the call must not make `c == 99` provable
        // after it, because the call overwrites `c`. Without the havoc in the goal, this
        // would pass and certify a stale value.
        let stale = Stmt::Assign { var: c, expr: smt::word(99, 8) };
        let s = Stmt::Seq {
            first: &init,
            second: &Stmt::Seq {
                first: &stale,
                second: &Stmt::Seq {
                    first: &call,
                    second: &Stmt::Assert(smt::eq(c, smt::word(99, 8))),
                },
            },
        };
        let r = wp::verify(&s, smt::truth(true), smt::truth(true));
        assert!(
            !r.is_verified(),
            "the call writes `c`, so its pre-call value 99 must not survive"
        );
    });
}

#[test]
fn a_call_to_a_never_returning_proc_is_not_total() {
    // A callee whose postcondition is unsatisfiable never returns: `ensures false` says
    // there is no state in which the call completes. A `Call` is modelled as "assume
    // `ensures`; continue", so that assumption is `false`, the continuation becomes
    // vacuous (`false => Q` is a theorem), and every claim after the call discharges for
    // free. With no loops in the program the report used to say `verified` / `Total` --
    // about a program that cannot get past the call.
    //
    // The callee is separately unverified, so this is not a claim about the callee: it is
    // that the *caller* was trusting a contract no run can satisfy and the report called
    // that progress. The finding is now `Rule::DivergentCall`, reported as a failure like
    // the other vacuity findings.
    smt::with_fresh(|| {
        let x = var(8);
        let boom = Proc {
            name: "boom",
            requires: smt::truth(true),
            ensures: smt::truth(false),
            body: &Stmt::Skip,
        };
        let call = Stmt::Call { proc_: &boom, actuals: &[], writes: &[] };
        let after = Stmt::Assign { var: x, expr: smt::word(7, 8) };
        let body = Stmt::Seq { first: &call, second: &after };

        let report = wp::verify(&body, smt::truth(true), x.eq_val(7));
        assert!(
            !report.is_verified(),
            "a call to a never-returning procedure must not verify: {:?}",
            report.correctness()
        );
        assert!(
            report.obligations[..report.count]
                .iter()
                .flatten()
                .any(|ob| ob.rule == Rule::DivergentCall),
            "the divergence must be attributed to the call"
        );
        // `correctness` asks about termination alone, so it must refuse this too rather
        // than seeing `loops == variants == 0` and calling it `Total`.
        assert!(
            !report.has_termination_proof(),
            "a divergent call is not a termination proof"
        );
    });
}

#[test]
fn a_call_to_a_proc_that_merely_returns_nothing_is_still_total() {
    // The control: a call to a procedure that returns normally -- `ensures true`, no
    // result pinned -- is not divergence, and must keep verifying. Without this the
    // `DivergentCall` check would pass by flagging every call.
    smt::with_fresh(|| {
        let x = var(8);
        let nop = Proc {
            name: "nop",
            requires: smt::truth(true),
            ensures: smt::truth(true),
            body: &Stmt::Skip,
        };
        let call = Stmt::Call { proc_: &nop, actuals: &[], writes: &[] };
        let after = Stmt::Assign { var: x, expr: smt::word(7, 8) };
        let body = Stmt::Seq { first: &call, second: &after };

        let report = wp::verify(&body, smt::truth(true), x.eq_val(7));
        assert!(report.is_verified(), "a normal call must still verify");
        assert!(
            !report.obligations[..report.count]
                .iter()
                .flatten()
                .any(|ob| ob.rule == Rule::DivergentCall),
            "a returning call must not be flagged as divergent"
        );
    });
}
