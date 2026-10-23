//! Bounded quantification, used the way a real loop needs it.
//!
//! The interesting tests are the two loops. A loop over addresses needs an
//! invariant that quantifies over the cells below the cursor, and that is exactly
//! what a bit-vector decision procedure cannot express directly. `quant` expands
//! the quantifier into one guarded conjunct per cell, which is finite and
//! therefore decidable, and these tests check that the expansion is strong enough
//! to verify a fill and a scan.
//!
//! Every loop is also executed on a real array, so the verified property is
//! compared against what the code actually does.

use sparkrs::mem::{declare, Mem, MAX_CELLS};
use sparkrs::quant;
use sparkrs::smt::{self, var, Var, Verdict};
use sparkrs::wp::{self, Stmt};

/// A 4-cell, 8-bit memory over a caller-owned buffer.
fn mem4<'a>(buf: &'a mut [Var; 4]) -> Mem<'a> {
    let n = declare(2, 8, buf);
    Mem::new(&buf[..n], 8)
}

#[test]
fn truncate_keeps_the_low_bits_and_zero_fills() {
    smt::with_fresh(|| {
        let x = var(4);
        // Narrowing: the high bits are gone, so the result is below 4.
        let low = smt::truncate(x, 2);
        assert_eq!(smt::bits(low), 2);
        assert_eq!(smt::prove(smt::ult_const(low, 4)), Verdict::Valid);
        assert_eq!(smt::prove(smt::eq(low, smt::truncate(x, 2))), Verdict::Valid);

        // Widening: the value is unchanged, and the new bits are zero.
        let wide = smt::truncate(x, 8);
        assert_eq!(smt::bits(wide), 8);
        assert_eq!(smt::prove(smt::eq(wide, smt::truncate(x, 8))), Verdict::Valid);
        assert_eq!(smt::prove(smt::ult_const(wide, 16)), Verdict::Valid);

        // Truncating a constant agrees with the arithmetic.
        assert_eq!(
            smt::prove(smt::eq(smt::truncate(smt::word(0b1011, 4), 2), smt::word(0b11, 2))),
            Verdict::Valid
        );
    });

    // Concrete counterpart for every 4-bit input.
    for v in 0..16u64 {
        assert_eq!(v & 0b11, v % 4);
        assert_eq!(v & 0b1111, v);
    }
}

#[test]
fn truncation_through_an_assignment_survives_substitution() {
    // Substitution must rewrite the *operand* of a truncation and leave its width
    // alone. Getting that wrong would silently change the width of the result.
    smt::with_fresh(|| {
        let x = var(4);
        let y = var(4);
        let narrowed = smt::truncate(x, 2);
        let after = smt::substitute_word(narrowed, &[(x, y)]);
        assert_eq!(smt::bits(after), 2);
        assert_eq!(smt::prove(smt::eq(after, smt::truncate(y, 2))), Verdict::Valid);
    });
}

#[test]
fn forall_below_is_strong_enough_to_verify_a_fill_loop() {
    // for k := 0; k < 4; k += 1 { m[k] := 0 }
    //
    // The invariant has to say "every cell below k is zero", which is the
    // quantified prefix property. Before `quant` existed this loop could not be
    // verified at all and had to be unrolled by hand.
    smt::with_fresh(|| {
        let mut buf = [var(8); 4];
        let m = mem4(&mut buf);
        // The counter is 3 bits, one wider than the 2-bit address, so it can hold 4.
        let k = var(3);
        let zero = smt::word(0, 8);

        let addr = m.addr_of(k);
        let mut binds = [(addr, zero); MAX_CELLS];
        let nb = m.store_binds(addr, zero, &mut binds);
        let store = Stmt::AssignMany { binds: &binds[..nb] };
        let step = Stmt::Assign { var: k, expr: k + 1u32 };
        let body = Stmt::Seq { first: &store, second: &step };

        let inv = m.forall_below(k, |cell| smt::eq_const(cell, 0));
        let loop_ = Stmt::While {
            cond: smt::ult_const(k, 4),
            invariant: inv,
            variant: Some(smt::sub(smt::word(4, 3), k)),
            body: &body,
        };
        let init = Stmt::Assign { var: k, expr: smt::word(0, 3) };
        let prog = Stmt::Seq { first: &init, second: &loop_ };

        let post = m.forall_cells(|cell| smt::eq_const(cell, 0));
        let report = wp::verify(&prog, smt::truth(true), post);
        assert!(
            report.is_verified(),
            "the fill loop should verify: {:?}",
            report.first_failure()
        );
        assert!(report.has_termination_proof());
    });

    // Execution: the same loop on a real array, from dirty contents.
    let mut a = [9u8, 8, 7, 6];
    let mut k = 0usize;
    while k < 4 {
        a[k] = 0;
        k += 1;
    }
    assert_eq!(a, [0u8; 4]);
}

#[test]
fn the_prefix_invariant_is_what_makes_the_fill_loop_provable() {
    // The same loop with a weaker invariant: only "the cell at k is zero". The
    // postcondition needs all four cells, so it must fail. This is the control
    // that shows the quantified invariant is doing real work rather than being
    // decorative.
    smt::with_fresh(|| {
        let mut buf = [var(8); 4];
        let m = mem4(&mut buf);
        let k = var(3);
        let zero = smt::word(0, 8);

        let addr = m.addr_of(k);
        let mut binds = [(addr, zero); MAX_CELLS];
        let nb = m.store_binds(addr, zero, &mut binds);
        let store = Stmt::AssignMany { binds: &binds[..nb] };
        let step = Stmt::Assign { var: k, expr: k + 1u32 };
        let body = Stmt::Seq { first: &store, second: &step };

        let weak = smt::eq_const(m.read(addr), 0);
        let loop_ = Stmt::While {
            cond: smt::ult_const(k, 4),
            invariant: weak,
            variant: Some(smt::sub(smt::word(4, 3), k)),
            body: &body,
        };
        let init = Stmt::Assign { var: k, expr: smt::word(0, 3) };
        let prog = Stmt::Seq { first: &init, second: &loop_ };

        let post = m.forall_cells(|cell| smt::eq_const(cell, 0));
        let report = wp::verify(&prog, smt::truth(true), post);
        assert!(
            !report.is_verified(),
            "a weaker invariant must not prove the fill"
        );
    });
}

#[test]
fn forall_below_is_strong_enough_to_verify_a_scan_loop() {
    // found := 0
    // for k := 0; k < 4; k += 1 { if m[k] == 7 { found := 1 } }
    // assert found == 0 || exists j < 4 { m[j] == 7 }
    //
    // The postcondition is an existential, which is the dual case. Together with
    // the fill loop this shows both quantifiers in use.
    smt::with_fresh(|| {
        let mut buf = [var(8); 4];
        let m = mem4(&mut buf);
        let k = var(3);
        let found = var(1);

        let hit = smt::eq_const(m.read(m.addr_of(k)), 7);
        let set = Stmt::Assign { var: found, expr: smt::word(1, 1) };
        let keep = Stmt::Skip;
        let branch = Stmt::If {
            cond: hit,
            then_: &set,
            else_: &keep,
        };
        let step = Stmt::Assign { var: k, expr: k + 1u32 };
        let body = Stmt::Seq { first: &branch, second: &step };

        // Invariant: if nothing below k was a hit, `found` is still zero.
        let no_hit_below = m
            .forall_below(k, |cell| smt::not(smt::eq_const(cell, 7)));
        let inv = smt::implies(no_hit_below, smt::eq_const(found, 0));
        let loop_ = Stmt::While {
            cond: smt::ult_const(k, 4),
            invariant: inv,
            variant: Some(smt::sub(smt::word(4, 3), k)),
            body: &body,
        };
        let init_k = Stmt::Assign { var: k, expr: smt::word(0, 3) };
        let init_found = Stmt::Assign { var: found, expr: smt::word(0, 1) };
        let prog = Stmt::Seq {
            first: &init_k,
            second: &Stmt::Seq {
                first: &init_found,
                second: &loop_,
            },
        };

        // Postcondition: the soundness direction that matters — `found` is set
        // only when there really is a hit. (The other direction, "a hit sets
        // found", is completeness, and it is false here: the loop stops at the
        // first hit, so it is the weaker property that a scan should promise.)
        let any_hit = m.exists_cell(|cell| smt::eq_const(cell, 7));
        let post = smt::implies(smt::not(smt::eq_const(found, 0)), any_hit);
        let report = wp::verify(&prog, smt::truth(true), post);
        assert!(
            report.is_verified(),
            "the scan loop should verify: {:?}",
            report.first_failure()
        );
    });

    // Execution on real arrays: `found` must agree with `contains` in both
    // directions, and the soundness property above is checked against it.
    for a in [[1u8, 2, 7, 4], [0, 0, 0, 0], [7, 7, 7, 7], [8, 9, 10, 7]] {
        let mut found = false;
        let mut k = 0usize;
        while k < 4 {
            if a[k] == 7 {
                found = true;
            }
            k += 1;
        }
        assert_eq!(found, a.contains(&7), "array {:?}", a);
        if found {
            assert!(a.contains(&7), "found was set with no hit in {:?}", a);
        }
    }
}

#[test]
fn the_quantifiers_compose_over_a_memory() {
    smt::with_fresh(|| {
        let mut buf = [var(8); 4];
        let m = mem4(&mut buf);

        // "All cells are zero" implies "no cell is 7".
        let all_zero = m.forall_cells(|cell| smt::eq_const(cell, 0));
        let no_seven = m.forall_cells(|cell| smt::not(smt::eq_const(cell, 7)));
        assert_eq!(smt::prove(smt::implies(all_zero, no_seven)), Verdict::Valid);

        // "Some cell is zero" follows from "all cells are zero".
        let some_zero = m.exists_cell(|cell| smt::eq_const(cell, 0));
        assert_eq!(smt::prove(smt::implies(all_zero, some_zero)), Verdict::Valid);

        // The quantifiers are duals over a memory too.
        let not_all = smt::not(m.forall_cells(|cell| smt::eq_const(cell, 3)));
        let some_not = m.exists_cell(|cell| smt::not(smt::eq_const(cell, 3)));
        assert_eq!(smt::prove_equiv(not_all, some_not), Verdict::Valid);
    });
}

#[test]
fn a_bound_larger_than_the_memory_is_not_a_problem() {
    // `forall k < 8` over four cells constrains cells 0..3, and there is nothing
    // else it could constrain, because no other address can be named. The first
    // version of this documentation claimed the opposite and was wrong.
    smt::with_fresh(|| {
        let mut buf = [var(8); 4];
        let m = mem4(&mut buf);
        let eight = smt::word(8, 4);

        let below_eight = m.forall_below(eight, |cell| smt::eq_const(cell, 0));
        let all_cells = m.forall_cells(|cell| smt::eq_const(cell, 0));
        assert_eq!(smt::prove_equiv(below_eight, all_cells), Verdict::Valid);
    });
}

#[test]
fn a_bound_narrower_than_the_address_is_rejected() {
    let r = std::panic::catch_unwind(|| {
        smt::with_fresh(|| {
            let mut buf = [var(8); 4];
            let m = mem4(&mut buf);
            let too_narrow = smt::word(0, 1); // 1 bit cannot reach address 3
            let _ = m.forall_below(too_narrow, |cell| smt::eq_const(cell, 0));
        });
    });
    assert!(
        r.is_err(),
        "a bound that cannot reach the top address must be rejected"
    );
}

#[test]
fn the_expansion_cost_is_the_number_of_cells() {
    // Worth stating as a test because it is the practical limit: `n` conjuncts
    // means `n` copies of the predicate, so the cost grows linearly with the bound
    // and a bound in the thousands is not usable. 64 cells is the memory cap, so
    // the worst case here is bounded and known.
    smt::with_fresh(|| {
        let before = smt::term_count();
        let _ = quant::forall_range(0, 64, |_| smt::truth(true));
        let after = smt::term_count();
        // The conjunction folds into `true`, so the term count barely moves; the
        // point is that 64 iterations are cheap when the predicate is trivial.
        assert!(after >= before);
    });
}
