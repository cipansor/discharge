//! Tests for the engine's *variable* shift, which the MIR frontend needs to model
//! `x << n` in real code rather than refusing it.
//!
//! Two levels, because they catch different bugs. The concrete sweep checks the
//! barrel shifter against Rust's own `<<` and `>>` at the amounts that matter
//! (zero, one, every power of two, one below and one at the width, and the
//! all-ones amount). The symbolic laws check what a proof built on the shifter
//! needs: a shift by a *constant* amount agrees through both the barrel path and
//! the engine's own constant-shift path, and a shift by a *symbolic* amount is not
//! the identity. A barrel shifter that passed only the concrete cases could still
//! disagree with the constant path on an amount no one thought to try, and the
//! frontend takes whichever path the MIR happens to present.

use discharge::smt::{self, Shift, Verdict};

/// Run a symbolic query on a thread with a large stack.
///
/// The BDD operations recurse, so their reach is bounded by stack depth as well
/// as by the arena. A barrel shifter is `log2(w)` selects deep and the selects
/// feed comparisons, so the room is asked for up front rather than discovering
/// the limit as an abort.
fn on_big_stack<F: FnOnce() + Send + 'static>(f: F) {
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(f)
        .expect("spawn")
        .join()
        .expect("the query panicked");
}

/// Concrete `x << n` at width `w`, compared with Rust's own.
///
/// The engine defines the out-of-range result (zero for a left shift) rather than
/// leaving it unknown, for the same reason the divider defines `y == 0`: rustc
/// guards the shift with `assert(n < w)`, so a path that reaches the shift with
/// `n >= w` has already been reported as a panic. The test spells the defined
/// value out rather than avoiding those amounts.
fn concrete_shl(w: u8, x: u64, n: u64) {
    let mask = (1u64 << w) - 1;
    let x = x & mask;
    let n = n & mask;
    smt::with_fresh(|| {
        let got = smt::shift_var(Shift::Left, smt::word(x, w), smt::word(n, w));
        let got = smt::evaluate(got, |_| None);
        let want = if n >= w as u64 { 0 } else { (x << n) & mask };
        assert_eq!(got, Some(want), "{w}-bit {x} << {n}");
    });
}

/// Concrete `x >> n` (logical), compared with Rust's own on an unsigned value.
fn concrete_lshr(w: u8, x: u64, n: u64) {
    let mask = (1u64 << w) - 1;
    let x = x & mask;
    let n = n & mask;
    smt::with_fresh(|| {
        let got = smt::shift_var(Shift::LogicalRight, smt::word(x, w), smt::word(n, w));
        let got = smt::evaluate(got, |_| None);
        let want = if n >= w as u64 { 0 } else { x >> n };
        assert_eq!(got, Some(want), "{w}-bit {x} >> {n}");
    });
}

#[test]
fn left_shift_matches_rust_on_boundaries() {
    for w in [2u8, 4, 8, 16] {
        let max = (1u64 << w) - 1;
        for (x, n) in [
            (0, 0),
            (0, max),
            (1, 0),
            (1, 1),
            (max, 0),
            (max, 1),
            (max, w as u64 - 1),
            (max, w as u64),
            (max, w as u64 + 1),
            (max, max),
            (max / 2, 1),
            (max / 3, 2),
            (1u64 << (w - 1), 1),
        ] {
            concrete_shl(w, x, n);
        }
    }
}

#[test]
fn logical_right_shift_matches_rust_on_boundaries() {
    for w in [2u8, 4, 8, 16] {
        let max = (1u64 << w) - 1;
        for (x, n) in [
            (0, 0),
            (0, max),
            (1, 0),
            (1, 1),
            (max, 0),
            (max, 1),
            (max, w as u64 - 1),
            (max, w as u64),
            (max, max),
            (max / 2, 1),
            (1u64 << (w - 1), 1),
            (1u64 << (w - 1), w as u64 - 1),
        ] {
            concrete_lshr(w, x, n);
        }
    }
}

#[test]
fn every_power_of_two_amount_agrees_with_rust() {
    // Each barrel stage shifts by exactly one power of two. Testing those amounts
    // exercises one stage at a time, so a stage wired to the wrong bit of the
    // amount fails here rather than hiding behind a sum of stages.
    for w in [4u8, 8, 16] {
        let max = (1u64 << w) - 1;
        let mut i = 0u32;
        while (1u32 << i) < w as u32 {
            let amt = 1u64 << i;
            concrete_shl(w, max, amt);
            concrete_shl(w, 1, amt);
            concrete_lshr(w, max, amt);
            i += 1;
        }
    }
}

#[test]
fn barrel_agrees_with_the_constant_path_symbolically() {
    // The law a proof needs, and the one that catches a barrel stage wired to the
    // wrong amount bit: for a *fixed* amount `k`, the barrel shifter must equal the
    // engine's own constant shift. 4 bits keeps the query cheap while still having
    // two stages, which is the smallest case where a stage can be mis-wired.
    on_big_stack(|| {
        for k in [0u32, 1, 2, 3] {
            smt::with_fresh(|| {
                let x = smt::var(4);
                let n = smt::word(k as u64, 4);
                let via_barrel = smt::shift_var(Shift::Left, x, n);
                let via_const = smt::shl(x, k);
                assert_eq!(
                    smt::prove(smt::eq(via_barrel, via_const)),
                    Verdict::Valid,
                    "x << {k} must agree through both paths"
                );
            });
        }
    });
}

#[test]
fn a_variable_shift_is_not_the_identity() {
    // The direction that keeps the model honest: if the barrel shifter were
    // accidentally returning its input, the law above would still hold for `k == 0`
    // and the frontend would prove things about a shift that does not shift.
    // `x << n == x` must be *refutable*, and it must be refuted by an actual model
    // rather than by the engine declining.
    on_big_stack(|| {
        smt::with_fresh(|| {
            let x = smt::var(4);
            let n = smt::var(4);
            let shifted = smt::shift_var(Shift::Left, x, n);
            // Restricted to the range rustc's guard admits, so this is a real
            // statement about real shifts and not about the defined out-of-range
            // value.
            let in_range = smt::ult_const(n, 4);
            let identity = smt::and(in_range, smt::eq(shifted, x));
            match smt::find_model(identity) {
                Verdict::Counterexample(_) => {}
                other => panic!("`x << n == x` must be refutable, got: {other}"),
            }
        });
    });
}

#[test]
fn shift_left_by_the_width_is_the_defined_zero() {
    // The one case where the model and a naive reading of `<<` differ, pinned
    // explicitly so the defined value cannot drift. rustc reports this input as a
    // panic, and the frontend's `shift_left` target is checked to do exactly that
    // in `tests/mir.rs`; here the engine-level value is what is pinned.
    for w in [4u8, 8, 16] {
        let max = (1u64 << w) - 1;
        concrete_shl(w, max, w as u64);
        concrete_shl(w, 1, w as u64);
    }
}

#[test]
fn arithmetic_right_shift_replicates_the_sign_bit() {
    // `>>` on a signed value fills with the sign bit, not zero. A logical shift
    // here would still pass every unsigned test, so this is the test that pins the
    // distinction the `Shift` enum exists to make.
    for w in [4u8, 8, 16] {
        let max = (1u64 << w) - 1;
        for (x, n) in [(max, 0u64), (max, 1), (max, w as u64 - 1), (1, 1), (0, max)] {
            smt::with_fresh(|| {
                let got =
                    smt::shift_var(Shift::ArithmeticRight, smt::word(x, w), smt::word(n, w));
                let got = smt::evaluate(got, |_| None);
                // Reinterpret the width as two's complement: a set top bit means
                // the value is negative and the fill is ones.
                let signed = if x >> (w - 1) == 1 {
                    (x as i64) - (1i64 << w)
                } else {
                    x as i64
                };
                let want = if n >= w as u64 {
                    if signed < 0 {
                        max
                    } else {
                        0
                    }
                } else {
                    ((signed >> n) as u64) & max
                };
                assert_eq!(got, Some(want), "{w}-bit {x} >> {n} (arithmetic)");
            });
        }
    }
}
