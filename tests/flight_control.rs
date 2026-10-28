//! The vacuity guard in `examples/flight_control.rs`, pinned so a narrowing of the
//! modelled width cannot pass silently.
//!
//! The example proves `clamped <= 4095 => clamped * 1000 <= 4 095 000` at 22 bits,
//! the first width that holds the product. The proof is only meaningful because 22
//! bits can *represent* the bound; at 16 bits the product wraps and the consequent
//! is true for every value, so the implication would hold for any antecedent.
//!
//! The guard that establishes this used to ask whether the *clamped* product could
//! exceed the bound. It cannot, at any width -- the clamp caps it at exactly
//! 4 095 000 -- so `!prove(scaled > 4 095 000).is_proved()` passed whether or not
//! the width could hold the bound, and the guard asserted nothing. The guard now
//! asks for a *model* of the **unclamped** product, which is satisfiable at 22 bits
//! (`raw = 4096`) and unsatisfiable at 16. This test pins both halves: if the guard
//! is reverted to the clamped predicate, `the_bound_is_refutable_at(22)` becomes
//! false and the first assertion fails.

use discharge::smt::{self, var, Verdict};

#[allow(dead_code)]
#[path = "../examples/flight_control.rs"]
mod flight_control;

#[test]
fn the_vacuity_guard_accepts_a_width_that_can_hold_the_bound() {
    smt::with_fresh(|| {
        assert!(
            flight_control::the_bound_is_refutable_at(22),
            "22 bits can represent 4 095 000, so the guard must accept the width; a guard \
             over the clamped product cannot, because the clamp caps it at the bound"
        );
    });
}

#[test]
fn the_vacuity_guard_rejects_a_width_that_cannot_hold_the_bound() {
    smt::with_fresh(|| {
        assert!(
            !flight_control::the_bound_is_refutable_at(16),
            "16 bits cannot represent 4 095 000, so the guard must reject the width"
        );
    });
}

/// The bug itself, stated as a fact about the *old* predicate: the clamped product
/// is never above the bound, at any width, which is why negating `is_proved()` on it
/// was vacuous. This is the control the fix's guard must differ from.
#[test]
fn a_clamped_product_is_never_above_the_bound_at_any_width() {
    for width in [16u8, 22] {
        smt::with_fresh(|| {
            let raw = var(width);
            let max = smt::word(4095, width);
            let clamped = smt::ite(raw.gt(max), max, raw);
            let scaled = clamped * 1000u32;
            assert_eq!(
                smt::find_model(scaled.gt_val(4_095_000)),
                Verdict::Unsat,
                "at {width} bits the clamped product must never exceed the bound, which is \
                 exactly why a guard over it asserted nothing"
            );
        });
    }
}
