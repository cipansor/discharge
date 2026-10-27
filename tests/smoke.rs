use discharge::mem;
use discharge::smt;
use discharge::smt::*;

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

#[test]
fn a_stale_variable_is_refused_not_misread() {
    // The fourteenth hole, found by asking "what else carries a term id, and what happens
    // when the arena moves on?". `Certificate` and `Report` were stamped, but a bare `Var`
    // or `Pred` — and `Mem`, and `Query` — carry a term id with no stamp. Reusing one after
    // a reset does not fail cleanly: the id names a different term, and the *old comment on
    // `with_fresh`* said exactly what that produces — "use-after-free in the term arena,
    // typically unbounded recursion rather than a clean panic". It was right. A stale `Var`
    // through `prove` overflowed the stack.
    //
    // The fix is one check at the arena's term accessors, so every handle-carrying type is
    // covered without each having to remember. A stale handle now yields `Unknown`.
    let x = smt::with_fresh(|| var(8));
    smt::with_fresh(|| {
        // Do not assert the exact verdict's identity beyond Unknown: the point is that it
        // is not `Valid` and does not recurse forever.
        let v = prove(eq(x, x));
        assert!(
            matches!(v, Verdict::Unknown),
            "a stale variable must be refused, got {}",
            v
        );
        assert!(!v.is_proved(), "a stale variable must never be reported as proved");
    });
}

#[test]
fn a_stale_memory_is_refused_not_misread() {
    // The same check covers `Mem`, which holds cell variables declared in some arena. Built
    // in a later arena, its ids name other terms and the memory is not the one declared —
    // and there is no way for the type to know, because the ids are just numbers.
    let mut cells = [Var::SENTINEL; 4];
    smt::with_fresh(|| {
        mem::declare(2, 8, &mut cells);
    });
    smt::with_fresh(|| {
        let m = mem::Mem::new(&cells, 8);
        let r = m.read(var(2));
        let v = prove(eq(r, r));
        assert!(
            matches!(v, Verdict::Unknown),
            "a stale memory must be refused, got {}",
            v
        );
    });
}

#[test]
fn the_sentinel_is_not_a_real_variable() {
    // `Var::SENTINEL` is the zero-filler for the fixed-size buffers in `wp`, and the
    // frame computation assumes it can never equal a live handle. That was false: the
    // sentinel was `Term(0)` and the allocator handed out ids from 0, so
    // `Var::SENTINEL == var(8)` held -- the opposite of the comment that promised slot 0
    // "is never a real variable". Every reader happens to be `[..n]`-counted, so nothing
    // broke, but an invariant a reviewer would rely on was not true. Term id 0 is now
    // reserved (`smt::TERM_SENTINEL`), and this pins that.
    smt::with_fresh(|| {
        let first = var(8);
        assert_ne!(first, Var::SENTINEL, "the first real variable is not the sentinel");
        // And no variable declared afterwards collides either.
        for _ in 0..64 {
            assert_ne!(var(8), Var::SENTINEL, "no real variable may equal the sentinel");
        }
    });
}

#[test]
fn fresh_handles_still_decide_normally() {
    // The teeth. A check that refused everything would pass the two tests above and break
    // the crate. Inside one arena, ordinary queries must still be decided.
    smt::with_fresh(|| {
        let x = var(8);
        assert!(prove(eq(x, x)).is_proved(), "a tautology must still be proved");
        assert!(
            matches!(prove(eq_const(x, 0)), Verdict::Counterexample(_)),
            "a satisfiable-but-not-valid statement must still be refuted"
        );
    });
    smt::with_fresh(|| {
        let mut cells = [Var::SENTINEL; 4];
        mem::declare(2, 8, &mut cells);
        let m = mem::Mem::new(&cells, 8);
        let r = m.read(var(2));
        // A fresh memory read is a real term of the declared width, and `r == r` is proved.
        assert_eq!(bits(r), 8, "a fresh read has the element width");
        assert!(prove(eq(r, r)).is_proved(), "a fresh memory query must still be decided");
    });
}
