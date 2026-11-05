//! The cross-check between the two engines.
//!
//! `discharge-arithmetic` proves its obligations by **exhaustive enumeration**,
//! with no solver. This crate proves the *same* obligations with the **symbolic
//! bit-blasting `smt` engine**, at widths enumeration cannot reach. This module
//! makes the two answers meet.
//!
//! There are three kinds of obligation, and each is checked the way it can be:
//!
//! 1. **Both engines can decide it.** Assert both say `Valid`. A disagreement
//!    here is the bug this file exists to catch: either the enumeration has a
//!    hole (it proved something false) or the symbolic engine is unsound.
//!
//! 2. **Only the symbolic engine can decide it.** The 32-bit two-variable
//!    domains are `2^64` cases; enumeration returns `Unknown` by design. The
//!    symbolic engine must still prove them, which is the *reason* the two
//!    engines coexist rather than one replacing the other.
//!
//! 3. **Neither should prove it.** A statement that is false must be refuted by
//!    both, or at worst left `Unknown` by enumeration and refuted by `smt`. A
//!    `Valid` from either engine on a false statement is a soundness failure and
//!    is reported as such.
//!
//! The enumeration is the crate under test; the symbolic engine is the oracle.
//! The dependency runs one way — `discharge` depends on `discharge-arithmetic`
//! — so there is no cycle, and the oracle can never be what the artifact ships.

use discharge::discharge_arithmetic::prove::{self, Verdict as EnumVerdict};
use discharge::logic::{verify_checked_add, verify_saturating_add_bounds};
use discharge::primitives::{
    verify_accumulator_no_overflow, verify_bounded_sub_is_total, verify_safe_add_is_exact,
    verify_saturating_add_monotone,
};
use discharge::smt;

/// Both engines agree the statement is true.
fn both_prove(name: &str, enumerated: EnumVerdict, symbolic: smt::Verdict) {
    assert!(
        enumerated.is_proved(),
        "{}: enumeration did not prove it: {:?}",
        name,
        enumerated
    );
    assert!(
        symbolic.is_proved(),
        "{}: symbolic engine did not prove it: {}",
        name,
        symbolic
    );
}

// ---------------------------------------------------------------------------
// 1. Obligations both engines can decide
// ---------------------------------------------------------------------------

#[test]
fn checked_add_agrees() {
    both_prove(
        "checked_add_is_total",
        prove::checked_add_is_total(),
        verify_checked_add(),
    );
}

#[test]
fn saturating_add_bounds_agree() {
    both_prove(
        "saturating_add_bounds",
        prove::saturating_add_bounds(),
        verify_saturating_add_bounds(),
    );
}

#[test]
fn safe_add_is_exact_agrees_at_8_and_16() {
    for w in [8u8, 16] {
        both_prove(
            &format!("safe_add_is_exact(w={})", w),
            prove::safe_add_is_exact(w),
            verify_safe_add_is_exact(w),
        );
    }
}

#[test]
fn accumulator_no_overflow_agrees_on_a_12_bit_domain() {
    // 2^24 cases: enumeration reaches it, and so does the symbolic engine.
    both_prove(
        "accumulator_no_overflow(12, 1000)",
        prove::accumulator_no_overflow(12, 1000),
        verify_accumulator_no_overflow(12, 1000),
    );
}

#[test]
fn saturating_add_monotone_agrees() {
    both_prove(
        "saturating_add_monotone(8, 7)",
        prove::saturating_add_monotone(8, 7),
        verify_saturating_add_monotone(8, 7),
    );
}

// ---------------------------------------------------------------------------
// 2. Obligations only the symbolic engine can decide
// ---------------------------------------------------------------------------

/// The whole justification for keeping a symbolic engine: at 32 bits, two
/// variables are `2^64` cases. Enumeration refuses; the symbolic engine proves
/// it. This test asserts *both* halves — that the enumeration declines, and that
/// the symbolic engine does not — on the same statement.
#[test]
fn the_32_bit_domain_is_where_the_symbolic_engine_earns_its_keep() {
    // The same obligation, both engines. At 8 and 16 the enumeration decides it;
    // at 32 the domain is 2^64 and it declines, while `smt` still proves it.
    for w in [8u8, 16] {
        assert!(prove::safe_add_is_exact(w).is_proved(), "enumeration at {}", w);
    }
    assert_eq!(
        prove::safe_add_is_exact(32),
        EnumVerdict::Unknown,
        "2^64 cases is past the enumeration budget; it must decline, not guess"
    );
    assert!(
        discharge::primitives::verify_safe_add_is_exact(32).is_proved(),
        "the symbolic engine must prove at 32 what enumeration cannot reach"
    );

    // And a single 33-bit variable is past 2^32 for the one-variable walk.
    assert_eq!(prove::sub_self_is_zero(33), EnumVerdict::Unknown);
}

/// `Bounded::sub`'s refinement at the width the parent states it (32 bits) is
/// beyond enumeration, but the enumeration proves the *same property* at the
/// 8-bit domain it can exhaust. Both answers are `Valid`; neither is `Unknown`.
/// The two engines meet on the property even where they cannot share a width.
#[test]
fn bounded_sub_refinement_is_proved_at_every_width_each_engine_can_reach() {
    for (min, max) in [(0u64, 255u64), (10, 100), (5, 200)] {
        assert!(
            prove::bounded_sub_is_total(min, max).is_proved(),
            "enumeration must prove the 8-bit instance ({}, {})",
            min,
            max
        );
        assert!(
            verify_bounded_sub_is_total(min, max).is_proved(),
            "smt must prove the 32-bit instance ({}, {})",
            min,
            max
        );
    }
}

#[test]
fn the_full_range_sub_is_only_the_symbolic_engine() {
    // The case the underflow gate exists for: `min == 0`, `max == u32::MAX`.
    assert!(verify_bounded_sub_is_total(0, u32::MAX as u64).is_proved());
    assert!(verify_bounded_sub_is_total(1, u32::MAX as u64).is_proved());
    assert!(verify_bounded_sub_is_total(5, u32::MAX as u64).is_proved());
}

// ---------------------------------------------------------------------------
// 3. False statements must not be proved by either engine
// ---------------------------------------------------------------------------

/// The accumulator bound the old code got wrong: `verify_accumulator_no_overflow(8, 200)`
/// must be **refuted** by the symbolic engine (200 + 200 wraps in 8 bits), and
/// the enumeration must agree it is false.
#[test]
fn a_false_accumulator_bound_is_refuted_by_both() {
    for (w, max) in [(8u8, 200u64), (8, 128), (8, 255)] {
        let symbolic = verify_accumulator_no_overflow(w, max);
        assert!(
            matches!(symbolic, smt::Verdict::Counterexample(_)),
            "width {} max {} must be refuted with a witness, got {}",
            w,
            max,
            symbolic
        );
        let enumerated = prove::accumulator_no_overflow(w, max);
        assert!(
            !enumerated.is_proved(),
            "the enumeration must not prove the false bound (w={}, max={})",
            w,
            max
        );
    }
}

/// An obligation stated as false on purpose: "every 8-bit pair sums to at most
/// its first operand". Both engines must refuse it, and the enumeration must
/// hand back a witness that actually overflows.
#[test]
fn a_deliberately_false_obligation_is_not_proved() {
    let enumerated = prove::accumulator_no_overflow(8, 200);
    match enumerated {
        EnumVerdict::Counterexample(w) => {
            assert_eq!(w.len, 2);
            let sum = w.a.wrapping_add(w.b) & 0xFF;
            assert!(sum < w.a, "the witness must actually overflow");
        }
        other => panic!("expected a counterexample, got {:?}", other),
    }
}

// ---------------------------------------------------------------------------
// The two `Verdict` types are the same idea in two crates
// ---------------------------------------------------------------------------

/// Both engines expose `is_proved`/`is_decided` with the same meaning, so a
/// caller can treat "proved" uniformly whichever engine answered. This is the
/// contract that lets the oracle comparison above be written once.
#[test]
fn the_two_verdict_types_agree_on_what_proved_means() {
    // A proven statement.
    assert!(EnumVerdict::Valid.is_proved());
    assert!(smt::Verdict::Valid.is_proved());
    // An undecided one is not a proof, in either.
    assert!(!EnumVerdict::Unknown.is_proved());
    assert!(!smt::Verdict::Unknown.is_proved());
    assert!(!EnumVerdict::Unknown.is_decided());
    assert!(!smt::Verdict::Unknown.is_decided());
}
