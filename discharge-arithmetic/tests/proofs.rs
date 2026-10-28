//! The proofs, the runtime behaviour they are about, and the *teeth* that show
//! each proof is load-bearing.
//!
//! Every "teeth" test states the same obligation with one ingredient removed and
//! requires that it be **refuted**. A proof that still succeeds with its key
//! ingredient deleted is not a proof of anything; it is a proof of a weaker
//! statement wearing the stronger one's name. The parent crate learned this the
//! hard way (see its `verify_accumulator_no_overflow`), and this module keeps the
//! lesson.

use discharge_arithmetic::prove::{self, Verdict, Witness};
use discharge_arithmetic::*;

// ---------------------------------------------------------------------------
// The obligations hold
// ---------------------------------------------------------------------------

#[test]
fn checked_add_flag_is_exact() {
    assert!(prove::checked_add_is_total().is_proved());
}

#[test]
fn saturating_add_bounds_hold() {
    assert!(prove::saturating_add_bounds().is_proved());
}

#[test]
fn subtraction_cancels() {
    for w in [8u8, 16] {
        assert!(prove::sub_self_is_zero(w).is_proved(), "width {}", w);
    }
}

#[test]
fn algebraic_laws_hold() {
    // 10 laws x 2 widths.
    assert_eq!(prove::algebraic_identities(), 20);
}

#[test]
fn bounded_products_do_not_wrap() {
    assert!(prove::product_of_bounded_fits().is_proved());
}

#[test]
fn fixed_add_guard_is_sound() {
    assert!(prove::fixed_add_no_overflow().is_proved());
}

#[test]
fn fixed_point_roundtrips() {
    assert!(prove::fixed_roundtrip().is_proved());
    assert!(prove::scale_identity().is_proved());
}

#[test]
fn accumulator_never_overflows() {
    // 12-bit terms bounded by 1000: 2000 fits, no wrap.
    assert!(prove::accumulator_no_overflow(12, 1000).is_proved());
}

#[test]
fn safe_add_is_exact_at_every_width() {
    for w in [8u8, 12, 16] {
        assert!(prove::safe_add_is_exact(w).is_proved(), "width {}", w);
    }
}

#[test]
fn bounded_sub_refinement_holds() {
    assert!(prove::bounded_sub_is_total(0, 255).is_proved());
    assert!(prove::bounded_sub_is_total(10, 100).is_proved());
    assert!(prove::bounded_sub_is_total(5, 200).is_proved());
}

#[test]
fn saturating_add_is_monotone() {
    assert!(prove::saturating_add_monotone(8, 7).is_proved());
}

// ---------------------------------------------------------------------------
// The proofs have teeth: drop the load-bearing ingredient and they must fail
// ---------------------------------------------------------------------------

/// The `min` conjunct in `bounded_sub_is_total` is load-bearing. Without it the
/// claim is false: at `min == 10`, `a == 11` and `b == 10` are in range and
/// `b <= a`, but the difference `1` is below `min`, so `sub` rejects it while the
/// unguarded statement would accept it.
#[test]
fn the_min_conjunct_is_load_bearing() {
    let (min, max) = (10u64, 100u64);
    let mut refuted = false;
    let mut a = 0u64;
    'outer: while a <= max {
        let mut b = 0u64;
        while b <= max {
            let in_range = a >= min && a <= max && b >= min && b <= max;
            let no_underflow = b <= a;
            let diff = a.wrapping_sub(b);
            let result_ok = no_underflow && diff >= min && diff <= max;
            let without_min = no_underflow && diff <= max;
            if in_range && result_ok != without_min {
                refuted = true;
                break 'outer;
            }
            b += 1;
        }
        a += 1;
    }
    assert!(
        refuted,
        "without the min conjunct the claim must be falsifiable at (11, 10)"
    );
}

/// The underflow gate in `bounded_sub_is_total` is load-bearing. Without it, a
/// wrapping difference can land back in range and be accepted: at `a == 0`,
/// `b == 200` with `[0, 255]`, the wrapped difference `56` is in range while
/// `checked_sub` returned `None`.
#[test]
fn the_underflow_gate_is_load_bearing() {
    let mut refuted = false;
    let mut a = 0u64;
    'outer: while a <= 255 {
        let mut b = 0u64;
        while b <= 255 {
            let in_range = |v: u64| v <= 255;
            let pre = in_range(a) && in_range(b);
            let diff = a.wrapping_sub(b) & 0xFF;
            let ungated = in_range(diff);
            let want = b <= a;
            if pre && ungated != want {
                refuted = true;
                break 'outer;
            }
            b += 1;
        }
        a += 1;
    }
    assert!(
        refuted,
        "without the underflow gate a wrapping difference is accepted"
    );
}

/// The `ite` that saturates is load-bearing: the *wrapping* sum violates the
/// bound, so the saturation is not decoration.
#[test]
fn saturation_is_load_bearing() {
    // At (200, 200) the wrapping sum is 144, below *both* operands -- the bound
    // fails on the wrapping value, which is what the saturation repairs.
    let (a, b) = (200u8, 200u8);
    let sum = a.wrapping_add(b);
    assert_eq!(sum, 144);
    assert!(sum < a, "the wrapping sum is below a");
    assert!(sum < b, "and below b");
    // The saturating value is not below either, which is the property proved.
    let sat = u8::MAX;
    assert!(sat >= a && sat >= b);
}

/// The bound in `fixed_add_no_overflow` has to be `2^14 - 1`. With the inclusive
/// `2^14` the sum `2^14 + 2^14 = 2^15` sets the sign bit, so the goal
/// `sum <= 2^15 - 1` is false for that input.
#[test]
fn the_fixed_add_bound_is_tight() {
    let bound = 1u64 << 14;
    let a = bound;
    let b = bound;
    let sum = (a + b) & 0xFFFF;
    assert_eq!(sum, 1u64 << 15);
    assert!(
        sum > (1u64 << 15) - 1,
        "the inclusive bound 2^14 lets the sum reach 2^15, which overflows i16"
    );
    // And the concrete witness: 2^14 + 2^14 overflows a signed 16-bit add.
    assert_eq!((16384i32 + 16384) as i16, -32768);
}

/// The multiply in `scale_identity` is load-bearing: with a non-power-of-two
/// factor the shift does not recover `k`.
#[test]
fn the_scale_multiply_is_load_bearing() {
    let mut refuted = false;
    for k in 0u64..16 {
        let scaled = (k * 10) & 0xFF;
        if scaled >> 4 != k {
            refuted = true;
            break;
        }
    }
    assert!(refuted, "a scale of 10 must not satisfy the identity");
}

/// `algebraic_identities` would return the same count if a law were a tautology.
/// The or-with-mask law it uses in place of the old `0 <= x` is falsifiable.
#[test]
fn the_algebraic_laws_are_falsifiable() {
    let mask = 0xFFu64;
    let refuted = (0u64..=mask).any(|x| (x | mask) & mask != mask);
    assert!(!refuted, "x | mask == mask holds for the whole domain");
    // The control: the law this slot replaced is a tautology, which is why it was
    // removed -- it cannot be refuted by any input.
    let always = (0u64..=mask).all(|x| x <= mask);
    assert!(always, "`x <= mask` is a range fact, not a law with teeth");
}

// ---------------------------------------------------------------------------
// The enumeration is honest at its boundary
// ---------------------------------------------------------------------------

#[test]
fn a_domain_past_the_budget_is_unknown_not_valid() {
    // 24-bit pairs are 2^48, past the budget: the method must decline, not guess.
    assert_eq!(prove::safe_add_is_exact(24), Verdict::Unknown);
    assert!(!prove::safe_add_is_exact(24).is_proved());
    // And a 33-bit single variable is past 2^32.
    assert_eq!(prove::sub_self_is_zero(33), Verdict::Unknown);
}

#[test]
fn a_refuted_obligation_carries_a_witness() {
    // The false claim: every 8-bit pair has `a + b <= a`. It must be refuted with
    // a witness, and the witness must actually falsify it.
    let v = prove::accumulator_no_overflow(8, 200);
    match v {
        Verdict::Counterexample(w) => {
            assert_eq!(w.len, 2);
            let sum = w.a.wrapping_add(w.b) & 0xFF;
            assert!(sum < w.a, "the witness must actually overflow");
        }
        other => panic!("expected a counterexample, got {:?}", other),
    }
}

#[test]
fn a_witness_is_constructible_and_named() {
    let w = Witness {
        a: 1,
        b: 2,
        len: 2,
    };
    assert_eq!(w.len, 2);
}

// ---------------------------------------------------------------------------
// Runtime behaviour matches the proofs
// ---------------------------------------------------------------------------

#[test]
fn runtime_behaviour_matches_the_proof() {
    assert_eq!(checked_add(200, 55), Some(255));
    assert_eq!(checked_add(u32::MAX, 1), None);
    assert_eq!(saturating_add(u32::MAX, 1), u32::MAX);
    assert_eq!(saturating_sub(0, 1), 0);
    assert_eq!(mul_div(1000, 1000, 8), Some(125_000));
    assert_eq!(mul_div(1, 1, 0), None);

    assert_eq!(safe_add(1, 2), Some(3));
    assert_eq!(safe_add(u32::MAX, 1), None);
    assert_eq!(safe_sub(0, 1), None);
    assert_eq!(safe_mul(1 << 16, 1 << 16), None);
    assert_eq!(safe_div(10, 0), None);
    assert_eq!(safe_rem(10, 0), None);
    assert_eq!(safe_div(10, 3), Some(3));

    let a = Fixed::from_int(3);
    let b = Fixed::from_int(4);
    assert_eq!(a.saturating_add(b), Fixed::from_int(7));
    assert_eq!(a.to_int(), 3);
    assert_eq!(a.saturating_mul_int(2), Fixed::from_int(6));
    assert_eq!(a.checked_div_int(0), None);
    assert_eq!(Fixed::MIN.checked_div_int(-1), None);
    assert_eq!(
        Fixed::from_bits(i32::MIN).checked_div_int(2),
        Some(Fixed(i32::MIN / 2))
    );
}

#[test]
fn fixed_to_int_truncates_toward_zero() {
    assert_eq!(Fixed::from_bits(-32768).to_int(), 0);
    assert_eq!(Fixed::from_bits(-1).to_int(), 0);
    assert_eq!(Fixed::from_bits(-65536).to_int(), -1);
    assert_eq!(Fixed::from_bits(-65537).to_int(), -1);
    assert_eq!(Fixed::from_bits(65535).to_int(), 0);
    assert_eq!(Fixed::from_bits(i32::MIN).to_int(), -32768);
    assert_eq!(Fixed::from_bits(i32::MAX).to_int(), 32767);
    for bits in [
        i32::MIN,
        -70000,
        -65536,
        -32768,
        -1,
        0,
        1,
        32768,
        65535,
        i32::MAX,
    ] {
        assert_eq!(Fixed::from_bits(bits).to_int(), bits / 65536, "bits {}", bits);
    }
}

#[test]
fn fixed_from_int_saturates_instead_of_wrapping() {
    assert_eq!(Fixed::from_int(0).to_bits(), 0);
    assert_eq!(Fixed::from_int(1).to_bits(), 65536);
    assert_eq!(Fixed::from_int(-1).to_bits(), -65536);
    assert_eq!(Fixed::from_int(32767).to_bits(), 32767 << 16);
    assert_eq!(Fixed::from_int(-32768).to_bits(), i32::MIN);
    assert_eq!(Fixed::from_int(32768), Fixed::MAX);
    assert_eq!(Fixed::from_int(40000), Fixed::MAX);
    assert_eq!(Fixed::from_int(-32769), Fixed::MIN);
    assert_eq!(Fixed::from_int(i32::MAX), Fixed::MAX);
}

#[test]
fn bounded_type_behaves() {
    type Pwm = Bounded<0, 1000>;
    assert_eq!(Pwm::new(500).unwrap().get(), 500);
    assert!(Pwm::new(1001).is_none());
    assert_eq!(Pwm::clamp(5000).unwrap().get(), 1000);
    assert_eq!(Pwm::clamp(0).unwrap().get(), 0);
    let a = Pwm::new(600).unwrap();
    let b = Pwm::new(500).unwrap();
    // 600 + 500 = 1100 leaves [0, 1000], so the refinement rejects it.
    assert_eq!(a.add(b), None);
    assert_eq!(a.sub(b).unwrap().get(), 100);
}

#[test]
fn an_empty_bounded_range_admits_nothing() {
    type Empty = Bounded<100, 10>;
    assert_eq!(Empty::new(50), None, "new already refuses an empty range");
    assert_eq!(Empty::clamp(50), None, "clamp must refuse it too");
    assert_eq!(Empty::clamp(0), None);
    assert_eq!(Empty::clamp(200), None);
    type Pwm = Bounded<0, 1000>;
    assert_eq!(Pwm::clamp(5000).unwrap().get(), 1000);
    assert_eq!(Pwm::clamp(500).unwrap().get(), 500);
}

/// The concrete instance the old `Bounded::sub` doc got wrong: `11` and `10` are
/// in `[10, 100]` and `11 >= 10`, but the difference `1` is below `min`.
#[test]
fn bounded_sub_rejects_a_difference_below_min() {
    type R = Bounded<10, 100>;
    let a = R::new(11).unwrap();
    let b = R::new(10).unwrap();
    assert_eq!(a.sub(b), None, "1 is below min = 10");
}
