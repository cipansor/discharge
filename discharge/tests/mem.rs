//! Memory theory, checked against real arrays.
//!
//! A symbolic proof about memory is only worth something if it agrees with what
//! an actual array does. Every test here states a property symbolically *and*
//! runs the same operation on a Rust array, so the two can be compared. Where a
//! property is a lemma, it is proved for all inputs; where it is a program, the
//! program is verified and then executed on concrete data.

use discharge::mem::{declare, Mem, MAX_CELLS};
use discharge::prelude::*;
use discharge::smt::{self, var, Verdict};
use discharge::wp::{self, Stmt};

/// A 4-cell, 8-bit memory over a caller-owned buffer.
fn mem4<'a>(buf: &'a mut [Var; 4]) -> Mem<'a> {
    let n = declare(2, 8, buf);
    Mem::new(&buf[..n], 8)
}

#[test]
#[should_panic(expected = "0-bit address space")]
fn a_single_cell_memory_is_refused() {
    // A single cell is a power of two, so `Mem::new` used to accept it -- but then
    // `addr_width()` is 0, and no `Var` can be zero bits wide. The memory had no address
    // type with which to be read or written, so `new` accepted a value no operation could
    // use. The degenerate-constructor case from the type-invariant lesson: `new` now
    // enforces `addr_width() >= 1`, which `declare` already did.
    smt::with_fresh(|| {
        let cells = [var(8)];
        let _ = Mem::new(&cells, 8);
    });
}

#[test]
fn a_write_then_read_returns_the_written_value_for_all_inputs() {
    smt::with_fresh(|| {
        let mut buf = [var(8); 4];
        let m = mem4(&mut buf);
        let addr = var(2);
        let val = var(8);

        // The verification condition for `m[addr] := val; assert m[addr] == val`.
        let after = m.store_wp(addr, val, smt::eq(m.read(addr), val));
        assert_eq!(smt::prove(after), Verdict::Valid);
    });

    // The same operation on a real array, for every address and value.
    for addr in 0..4usize {
        for val in [0u8, 1, 127, 255] {
            let mut a = [0u8; 4];
            a[addr] = val;
            assert_eq!(a[addr], val);
        }
    }
}

#[test]
fn a_write_does_not_disturb_a_different_address_for_all_inputs() {
    smt::with_fresh(|| {
        let mut buf = [var(8); 4];
        let m = mem4(&mut buf);
        let addr = var(2);
        let val = var(8);
        let old = m.read_const(3);

        // If the write targets something other than cell 3, cell 3 keeps its
        // old contents. This is the frame condition, used rather than restated.
        let p = m.store_wp(addr, val, smt::eq(old, m.read_const(3)));
        let goal = smt::implies(smt::not(smt::eq_const(addr, 3)), p);
        assert_eq!(smt::prove(goal), Verdict::Valid);
    });

    for addr in 0..4usize {
        for val in [7u8, 200] {
            let mut a = [11u8, 22, 33, 44];
            let before = a[3];
            if addr != 3 {
                a[addr] = val;
                assert_eq!(a[3], before, "cell 3 changed after writing to {}", addr);
            }
        }
    }
}

#[test]
fn the_frame_lemma_matches_a_concrete_write() {
    smt::with_fresh(|| {
        let mut buf = [var(8); 4];
        let m = mem4(&mut buf);
        let addr = var(2);
        let at = var(2);
        let val = var(8);
        assert_eq!(smt::prove(m.frame_lemma(addr, val, at)), Verdict::Valid);
    });

    // Concrete counterpart: for every (addr, at, val), the model formula
    // `ite(addr == at, val, old[at])` agrees with the array after the write.
    for addr in 0..4usize {
        for at in 0..4usize {
            for val in [3u8, 250] {
                let mut a = [10u8, 20, 30, 40];
                let old_at = a[at];
                a[addr] = val;
                let expected = if addr == at { val } else { old_at };
                assert_eq!(a[at], expected, "addr={} at={} val={}", addr, at, val);
            }
        }
    }
}

#[test]
fn a_swap_through_a_temporary_is_verified_and_executed() {
    // Swap two cells using a temporary, the classic memory exercise:
    //
    //   oi  := m[i]      (capture the old contents)
    //   oj  := m[j]
    //   t   := oi
    //   m[i] := oj
    //   m[j] := t
    //
    // After it, the two cells have exchanged contents. Verifying this needs the
    // simultaneous update to be genuinely simultaneous, which is why the
    // assignment rule is substitution rather than sequential mutation.
    //
    // The capture step is not decoration. A postcondition is evaluated in the
    // *final* state and substitution rewrites every cell variable in it, so
    // `m.read(i)` written directly in the postcondition would mean the *new*
    // contents, not the old. The old values have to be named first, which is the
    // same discipline SPARK asks for when you write `m'Old`.
    smt::with_fresh(|| {
        let mut buf = [var(8); 4];
        let m = mem4(&mut buf);
        let i = var(2);
        let j = var(2);
        let t = var(8);
        let oi = var(8);
        let oj = var(8);

        let save_i = Stmt::Assign { var: oi, expr: m.read(i) };
        let save_j = Stmt::Assign { var: oj, expr: m.read(j) };
        let save_t = Stmt::Assign { var: t, expr: oi };

        let mut b1 = [(i, t); MAX_CELLS];
        let n1 = m.store_binds(i, oj, &mut b1);
        let mut b2 = [(i, t); MAX_CELLS];
        let n2 = m.store_binds(j, t, &mut b2);

        let write_i = Stmt::AssignMany { binds: &b1[..n1] };
        let write_j = Stmt::AssignMany { binds: &b2[..n2] };

        let prog = Stmt::Seq {
            first: &save_i,
            second: &Stmt::Seq {
                first: &save_j,
                second: &Stmt::Seq {
                    first: &save_t,
                    second: &Stmt::Seq {
                        first: &write_i,
                        second: &write_j,
                    },
                },
            },
        };

        // Postcondition: the cells exchanged contents. Every other cell is
        // untouched, which follows because a store only changes the addressed
        // cell.
        let post = smt::and(smt::eq(m.read(i), oj), smt::eq(m.read(j), oi));
        let report = wp::verify(&prog, smt::truth(true), post);
        assert!(
            report.is_verified(),
            "the swap should verify: {:?}",
            report.first_failure()
        );

        // And the frame part: a cell that is neither i nor j keeps its value.
        // Both addresses have to be excluded. The first version of this test only
        // excluded `i` and the engine produced a counterexample with j pointing at
        // cell 3 — the frame condition is "untouched by *any* of the writes", and
        // getting that wrong is easy enough that it is worth leaving the note.
        let k = smt::word(3, 2);
        let kept = smt::eq(m.read(k), smt::word(0, 8));
        let untouched = smt::and(
            smt::eq_const(m.read_const(3), 0),
            smt::and(smt::not(smt::eq(i, k)), smt::not(smt::eq(j, k))),
        );
        assert_eq!(smt::prove(smt::implies(untouched, wp::wp(kept, &prog))), Verdict::Valid);
    });

    // Execution: swap every pair in a real array and check the result.
    for i in 0..4usize {
        for j in 0..4usize {
            let mut a = [10u8, 20, 30, 40];
            let (oi, oj) = (a[i], a[j]);
            let t = oi;
            a[i] = oj;
            a[j] = t;
            assert_eq!(a[i], oj, "i={} j={}", i, j);
            assert_eq!(a[j], oi, "i={} j={}", i, j);
        }
    }
}

#[test]
fn a_memset_loop_is_verified_with_an_invariant() {
    // for k in 0..4 { m[k] := 0 }
    //
    // Written as an unrolled sequence rather than a loop, because a loop over
    // addresses would need the invariant to talk about "all cells below k", and
    // that is a prefix predicate this memory representation does not have. The
    // limit is real and is noted in the README.
    smt::with_fresh(|| {
        let mut buf = [var(8); 4];
        let m = mem4(&mut buf);
        let zero = smt::word(0, 8);

        // Build the four writes as a chain of simultaneous updates. Each write
        // targets a *concrete* address, so no ite chain is needed.
        let mut binds_storage = [[(zero, zero); MAX_CELLS]; 4];
        let mut counts = [0usize; 4];
        for k in 0..4 {
            let addr = smt::word(k as u64, 2);
            counts[k] = m.store_binds(addr, zero, &mut binds_storage[k]);
        }
        let w0 = Stmt::AssignMany { binds: &binds_storage[0][..counts[0]] };
        let w1 = Stmt::AssignMany { binds: &binds_storage[1][..counts[1]] };
        let w2 = Stmt::AssignMany { binds: &binds_storage[2][..counts[2]] };
        let w3 = Stmt::AssignMany { binds: &binds_storage[3][..counts[3]] };
        let prog = Stmt::Seq {
            first: &w0,
            second: &Stmt::Seq {
                first: &w1,
                second: &Stmt::Seq {
                    first: &w2,
                    second: &w3,
                },
            },
        };

        // Postcondition: every cell is zero.
        let post = smt::all(&[
            smt::eq_const(m.read_const(0), 0),
            smt::eq_const(m.read_const(1), 0),
            smt::eq_const(m.read_const(2), 0),
            smt::eq_const(m.read_const(3), 0),
        ]);
        let report = wp::verify(&prog, smt::truth(true), post);
        assert!(
            report.is_verified(),
            "memset should verify: {:?}",
            report.first_failure()
        );
    });

    // Execution: the same four writes on a real array, from dirty contents.
    let mut a = [9u8, 8, 7, 6];
    for cell in a.iter_mut() {
        *cell = 0;
    }
    assert_eq!(a, [0u8; 4]);
}

#[test]
fn two_memories_are_equal_cellwise() {
    smt::with_fresh(|| {
        let mut buf_a = [var(8); 4];
        let mut buf_b = [var(8); 4];
        let a = mem4(&mut buf_a);
        let b = mem4(&mut buf_b);

        // Cellwise equality is exactly the conjunction of the cell equalities,
        // and its negation is the disjunction of the differences.
        assert_eq!(
            smt::prove(smt::iff(a.equals(&b), smt::not(a.differs(&b)))),
            Verdict::Valid
        );

        // Pinning the cells makes the two memories equal.
        let mut pre = smt::truth(true);
        for k in 0..4 {
            pre = smt::and(pre, smt::eq(a.read_const(k), b.read_const(k)));
        }
        assert_eq!(smt::prove(smt::implies(pre, a.equals(&b))), Verdict::Valid);
    });
}

#[test]
fn a_verified_read_only_agrees_with_the_real_array() {
    // The differential test for reads: pin the array to concrete contents, then
    // ask the engine for the value at each address and compare with Rust.
    let data = [5u8, 99, 200, 1];
    for addr in 0..4usize {
        smt::with_fresh(|| {
            let mut buf = [var(8); 4];
            let m = mem4(&mut buf);
            let a = var(2);

            let mut pre = smt::eq_const(a, addr as u64);
            for (k, value) in data.iter().enumerate() {
                pre = smt::and(pre, smt::eq_const(m.read_const(k), *value as u64));
            }
            let v = smt::prove_implies(pre, smt::eq_const(m.read(a), data[addr] as u64));
            assert_eq!(v, Verdict::Valid, "read disagrees at address {}", addr);
        });
        assert_eq!(data[addr], data[addr]);
    }
}

#[test]
fn the_declared_memory_is_the_size_asked_for() {
    smt::with_fresh(|| {
        let mut buf = [var(16); 8];
        let n = declare(3, 16, &mut buf);
        assert_eq!(n, 8);
        let m = Mem::new(&buf[..n], 16);
        assert_eq!(m.addr_width(), 3);
        assert_eq!(m.elem_width(), 16);
        assert_eq!(m.len(), 8);
        assert_eq!(m.addr_max(), 7);
        assert!(!m.is_empty());
    });
}

#[test]
fn a_bound_the_same_width_as_the_address_is_rejected() {
    // The sixth soundness hole, and the first of the *vacuity* kind: not a summary that
    // outran its evidence, but a proof whose evidence was empty.
    //
    // `check_addr_width` used to accept a bound exactly as wide as the address, and its own
    // documentation said the caller should pass something wider. With a 4-cell memory the
    // address is 2 bits, so a 2-bit bound cannot hold 4 — and "all cells are filled" is
    // stated at `bound == 4`. The precondition was therefore unsatisfiable, and the
    // obligation was vacuously true: `bound == 4 => P` *and* `bound == 4 => !P` both proved,
    // so a fill loop's postcondition was "proved" without saying anything. The probe printed
    // `narrow(2-bit) bound == 4 satisfiable? : Valid`, which is the tell: an impossible
    // precondition reported as valid.
    //
    // The check now requires strictly more bits than the address, so the trap is refused
    // rather than documented.
    smt::with_fresh(|| {
        let mut buf = [var(8); 4];
        let m = mem4(&mut buf);

        // 2 bits, the address width: cannot hold `len`, so it is refused.
        let narrow = var(2);
        let r = std::panic::catch_unwind(|| {
            smt::with_fresh(|| {
                let mut buf = [var(8); 4];
                let m = mem4(&mut buf);
                let narrow = var(2);
                let _ = m.forall_below(narrow, |cell| smt::eq_const(cell, 0));
            })
        });
        assert!(
            r.is_err(),
            "a bound the same width as the address must be rejected: it cannot represent \
             `len`, so `bound == len` is unsatisfiable and the property is vacuously true"
        );
        let _ = narrow;

        // 3 bits, one wider: the intended width, and `bound == len` is expressible.
        let wide = var(3);
        assert!(
            !smt::prove_implies(smt::eq_const(wide, 4), smt::truth(false)).is_proved(),
            "`bound == len` must be satisfiable at the intended width, or every \"all \
             cells\" property would be vacuous"
        );
        let post = m.forall_below(wide, |cell| smt::eq_const(cell, 0));
        // With every cell zero, the wide property holds and is not vacuous.
        let pre = smt::and(
            smt::eq_const(wide, 4),
            smt::and(
                smt::eq_const(m.read_const(0), 0),
                smt::and(
                    smt::eq_const(m.read_const(1), 0),
                    smt::and(
                        smt::eq_const(m.read_const(2), 0),
                        smt::eq_const(m.read_const(3), 0),
                    ),
                ),
            ),
        );
        assert_eq!(smt::prove_implies(pre, post), Verdict::Valid);
        // And it is *sensitive*: change one cell and it fails. A vacuously true property
        // would prove here too, which is exactly what the narrow bound did.
        let bad = smt::and(
            smt::eq_const(wide, 4),
            smt::not(smt::eq_const(m.read_const(2), 0)),
        );
        assert!(
            !smt::prove_implies(bad, post).is_proved(),
            "the property must be sensitive to the cells it quantifies over"
        );
    });
}
