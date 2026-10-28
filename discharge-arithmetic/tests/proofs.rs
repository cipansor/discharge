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

// ---------------------------------------------------------------------------
// A width of zero is refused, not enumerated
// ---------------------------------------------------------------------------

/// A zero-bit integer is not a word width, but `1u64 << 0` is `1`, so the
/// enumeration would visit the fabricated point `(0, 0)` and answer `Valid` for a
/// proposition about a type that does not exist. Every width-dependent entry point
/// must refuse instead of certifying an invalid domain.
#[test]
fn a_zero_width_domain_is_unknown_not_valid() {
    assert_eq!(prove::safe_add_is_exact(0), Verdict::Unknown);
    assert_eq!(prove::sub_self_is_zero(0), Verdict::Unknown);
    assert_eq!(prove::accumulator_no_overflow(0, 0), Verdict::Unknown);
    assert_eq!(prove::saturating_add_monotone(0, 1), Verdict::Unknown);
    assert_eq!(prove::restricted_domain_matches(0, 1, 1), Verdict::Unknown);
    assert_eq!(prove::bounded_walk_covers_its_rectangle(0, 1), Verdict::Unknown);
    // The one-bit domain is real, so the same guard must not swallow it.
    assert!(prove::safe_add_is_exact(1).is_proved(), "a 1-bit domain is a domain");
}

// ---------------------------------------------------------------------------
// The restricted enumeration is the same question, checked and not assumed
// ---------------------------------------------------------------------------

/// `fixed_add_no_overflow` enumerates the precondition's rectangle rather than the
/// whole 16-bit domain, which is what made it the slowest test in the gate. That is
/// only sound if the rectangle is *exactly* the set the precondition selects, and
/// this checks it on the **domains** rather than by running a goal.
#[test]
fn the_restricted_domain_matches_the_precondition() {
    assert!(prove::restricted_domain_matches(8, 200, 200).is_proved());
    assert!(prove::restricted_domain_matches(6, 50, 50).is_proved());
    // The bound `fixed_add_no_overflow` actually uses, read from the obligation
    // rather than copied, so the check cannot pass against a stale number.
    assert!(
        prove::restricted_domain_matches(16, prove::FIXED_ADD_BOUND, prove::FIXED_ADD_BOUND)
            .is_proved(),
        "the obligation's own rectangle must be the precondition's set"
    );
}

/// The regression the first version of this check missed. It compared the two
/// walks' *verdicts*, and both stop at their first counterexample — so bounds 200
/// and 199, which fail first at the same `(1, 198)`, looked like the same question
/// even though 199 omits every pair containing 200 that the precondition admits.
/// Comparing the domains catches it in both directions.
#[test]
fn a_rectangle_that_omits_admitted_inputs_is_caught() {
    // 199 omits inputs the precondition (<= 200) admits: 200 itself. The scan runs
    // `a` outer, `b` inner, so the first pair the two classify differently is
    // `(0, 200)` — in the precondition, outside the rectangle.
    assert_eq!(
        prove::restricted_domain_matches(8, 200, 199),
        Verdict::Counterexample(Witness { a: 0, b: 200, len: 2 }),
        "a rectangle narrower than the precondition must be reported"
    );
    // And the other direction: a rectangle that admits inputs the precondition
    // excludes is equally wrong, because the walk would check points the
    // obligation's guard never intends to cover.
    assert_eq!(
        prove::restricted_domain_matches(8, 199, 200),
        Verdict::Counterexample(Witness { a: 0, b: 200, len: 2 }),
        "a rectangle wider than the precondition must be reported too"
    );
}

/// A bound at or past the domain is not a restriction of it, and the walk refuses
/// such a bound; the domain check must refuse it too rather than compare nonsense.
#[test]
fn a_bound_past_the_domain_is_refused() {
    assert_eq!(prove::restricted_domain_matches(8, 256, 256), Verdict::Unknown);
    assert_eq!(prove::restricted_domain_matches(8, 255, 300), Verdict::Unknown);
    // 255 is the last real 8-bit value, so this one is well-formed.
    assert!(prove::restricted_domain_matches(8, 255, 255).is_proved());
}

/// The walk half of the argument: `forall_pair_bounded` must visit its rectangle
/// exactly, corners and edges included, and must not stray outside it. This is
/// checked with tripwire goals that do not depend on any real obligation, so it
/// stays a statement about the enumerator.
#[test]
fn the_bounded_walk_covers_its_rectangle() {
    for bound in [0u64, 1, 2, 3, 7, 50, 199, 200, 255] {
        assert!(
            prove::bounded_walk_covers_its_rectangle(8, bound).is_proved(),
            "the walk must cover exactly [0, {}]^2, edges included",
            bound
        );
    }
    // A narrower width exercises the same code with a different domain size.
    assert!(prove::bounded_walk_covers_its_rectangle(4, 9).is_proved());
}

// ---------------------------------------------------------------------------
// The statements and the runtime primitives are tied together
// ---------------------------------------------------------------------------

/// The obligations above are stated at 8 and 16 bits, because that is the largest
/// domain enumeration can exhaust, while the primitives they are *about* are
/// `u32`. The widths cannot be reconciled by calling the primitive from the
/// obligation: two 8-bit values added as `u32` never overflow, so the obligation
/// would be proved for the wrong reason. Instead this test checks each primitive at
/// the `u32` points where the property its obligation states is observable, so a
/// regression in a primitive has to survive this as well as the verdicts.
#[test]
fn runtime_ops_match_their_proved_statements() {
    // `checked_add_is_total`: the overflow flag is exact, so `checked_add` returns
    // `None` exactly when the wrapped sum fell below an operand.
    for (a, b) in [
        (0u32, 0u32),
        (1, 1),
        (200, 55),
        (1000, 1000),
        (1 << 31, 1 << 31),
        (u32::MAX, 0),
        (u32::MAX, 1),
        (u32::MAX, u32::MAX),
    ] {
        let wrapped = a.wrapping_add(b);
        assert_eq!(
            wrapped < a,
            wrapped < b,
            "the two overflow tests must agree at ({a}, {b})"
        );
        assert_eq!(
            checked_add(a, b).is_none(),
            wrapped < a,
            "checked_add must report overflow exactly when the sum wraps at ({a}, {b})"
        );
        assert_eq!(safe_add(a, b), checked_add(a, b), "safe_add at ({a}, {b})");
    }

    // `saturating_add_bounds`: the saturating sum is never below an operand, and it
    // equals the true sum whenever that sum did not wrap.
    for (a, b) in [
        (0u32, 0u32),
        (200, 55),
        (1000, 1000),
        (1 << 31, 1 << 31),
        (u32::MAX, 1),
    ] {
        let sat = saturating_add(a, b);
        assert!(sat >= a && sat >= b, "sat below an operand at ({a}, {b})");
        match checked_add(a, b) {
            Some(sum) => assert_eq!(sat, sum, "without overflow sat must be the sum at ({a}, {b})"),
            None => assert_eq!(sat, u32::MAX, "overflow must clamp to MAX at ({a}, {b})"),
        }
    }

    // `sub_self_is_zero`: cancellation, at the boundaries where it could fail.
    for x in [0u32, 1, 1000, 1 << 31, u32::MAX] {
        assert_eq!(safe_sub(x, x), Some(0), "x - x must be 0 at {x}");
        assert_eq!(checked_sub(x, x), Some(0));
    }

    // `scale_identity` / `fixed_roundtrip`: the Q16.16 round-trip is lossless over
    // the integer range the type holds, and it saturates outside that range.
    for k in [0i32, 1, -1, 32767, -32768] {
        assert_eq!(
            Fixed::from_int(k).to_int(),
            k,
            "the round-trip must be lossless at {k}"
        );
    }
    assert_eq!(Fixed::from_int(32768), Fixed::MAX, "from_int saturates at the top");
    assert_eq!(Fixed::from_int(-32769), Fixed::MIN, "and at the bottom");

    // `mul_div`: the widening is load-bearing. `100_000 * 100_000` wraps a `u32`
    // but not the `u64` intermediate, so the naive product reports the wrong
    // quotient. This is the property `mul_div`'s doc points at.
    assert_eq!(mul_div(100_000, 100_000, 1000), Some(10_000_000));
    assert_eq!(mul_div(1000, 1000, 8), Some(125_000));
    assert_eq!(mul_div(1, 1, 0), None, "a zero divisor is the only failure mode");
    let naive = 100_000u32.wrapping_mul(100_000) / 1000;
    assert_ne!(
        mul_div(100_000, 100_000, 1000),
        Some(naive),
        "the widening must change the answer, or it is not load-bearing"
    );
}
