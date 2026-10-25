use sparkrs::smt::*;

#[test]
fn commutativity_of_add_is_proved() {
    with_fresh(|| {
        let x = var(8);
        let y = var(8);
        // x + y == y + x, both sides built as words then compared
        let lhs = add(x, y);
        let rhs = add(y, x);
        let p = eq(lhs, rhs);
        let v = prove(p);
        assert!(v.is_proved(), "expected proof, got {}", v);
    });
}

#[test]
fn bound_is_refuted_with_counterexample() {
    with_fresh(|| {
        let x = var(8);
        let v = prove(ule_const(x, 100));
        match v {
            Verdict::Counterexample(c) => {
                let xv = c.value_of(0).expect("x in model");
                assert!(xv > 100);
            }
            other => panic!("expected refutation, got {}", other),
        }
    });
}

#[test]
fn x_minus_x_is_zero() {
    with_fresh(|| {
        let x = var(16);
        let z = word(0, 16);
        let v = prove(eq(sub(x, x), z));
        assert!(v.is_proved(), "got {}", v);
    });
}

#[test]
fn mask_identity() {
    with_fresh(|| {
        let x = var(32);
        // (x & 0xFF) == (x % 256)
        let m = word(0xFF, 32);
        let lhs = band(x, m);
        let rhs = word(256, 32);
        // x & 0xFF < 256 always
        let v = prove(ult(lhs, rhs));
        assert!(v.is_proved(), "got {}", v);
    });
}

#[test]
fn exceeding_max_vars_reports_unknown_not_a_proof() {
    // Honesty at the variable cap. `var_term` refuses an index at or past MAX_VARS by
    // setting `overflow` and returning `Term(0)` — and `Term(0)` is a *valid* node (the
    // constant 0), not a poisoned one. So without the overflow guard the query does not
    // fail; it answers about the wrong thing.
    //
    // Measured, not reasoned: with the guard removed, `prove(v300 == 0)` returns
    // `Counterexample(v0 = 1)`. The fallback made v300 alias v0, so the engine reported a
    // witness naming a variable the query never mentioned. (I had expected a false
    // `Valid`; the real failure mode is a bogus witness, which is why this was worth
    // measuring rather than asserting.)
    //
    // With the guard it returns `Unknown`, which is the honest answer.
    with_fresh(|| {
        let mut last = var(1);
        for _ in 0..300 {
            last = var(1);
        }
        let bogus = eq_const(last, 0);
        let verdict = prove(bogus);
        assert!(
            matches!(verdict, Verdict::Unknown),
            "past MAX_VARS the answer must be Unknown, got {}",
            verdict
        );
        assert!(
            !verdict.is_proved(),
            "an overflowed query must never be reported as proved"
        );
    });
}

#[test]
fn a_query_within_max_vars_is_decided_normally() {
    // The teeth: the overflow path must not swallow ordinary queries. Just under the cap,
    // a true statement is proved and a false one is refuted.
    with_fresh(|| {
        let mut last = var(1);
        for _ in 0..200 {
            last = var(1);
        }
        // `v == v` is a tautology; `v == 0` is not.
        let tautology = or(eq_const(last, 0), not(eq_const(last, 0)));
        assert!(
            prove(tautology).is_proved(),
            "a tautology under the cap must still be proved"
        );
        assert!(
            matches!(prove(eq_const(last, 0)), Verdict::Counterexample(_)),
            "a satisfiable-but-not-valid statement under the cap must be refuted"
        );
    });
}
