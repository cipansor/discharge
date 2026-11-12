//! Regression test: the complement of a literal (`!0`, `!4`) has no type of its
//! own, so a contract that puts one in a *signed* context must not read it as
//! unsigned.
//!
//! Rust infers a literal's type from the operand it meets, and `!` propagates
//! that type. For `ret: i8`, `!0` is `-1` and `!0 >> 1` is `-1` (an arithmetic
//! shift), so `ensures: ret <= (!0 >> 1)` means `ret <= -1`. The reader used to
//! give a literal the *unsigned* flag and `!` carried it through, so it built
//! `255u8 >> 1` as a *logical* shift and read the bound as `127` — discharging the
//! postcondition for every `i8`, a false proof.
//!
//! The fix carries an explicit `Sign` state through the parser. A typed operand
//! fixes an untyped partner's sign; where there is no typed operand and the two
//! readings differ (`>>`, `/`, `%`, an ordering comparison, a widening cast), the
//! shape is refused rather than guessed.

use verif::mir::spec;
use verif::smt;
use std::collections::{BTreeMap, BTreeSet};

/// Parse an `ensures:` clause for a function returning `i8`, with `x` an `i8`
/// argument in scope. Returns `Ok(predicate)` or the refusal.
fn ensures(text: &str) -> Result<smt::Pred, spec::SpecError> {
    let mut args = BTreeMap::new();
    args.insert("x".to_string(), smt::var_named(0, 8));
    let ret = smt::var_named(1, 8);
    let mut signed = BTreeSet::new();
    signed.insert("x".to_string());
    spec::eval_ensures(
        text,
        &args,
        Some(ret),
        spec::RET_IS_UNKNOWN,
        &signed,
        true, // `ret` is `i8`
        &spec::FieldEnv::default(),
    )
}

/// The reader must not *prove* a postcondition that Rust evaluates to `false`.
#[test]
fn the_complement_of_a_literal_is_not_read_as_unsigned() {
    smt::with_fresh(|| {
        // The false proof. Either the shape is refused, or it is read as signed
        // (`ret <= -1`, which the engine then refutes — not proves).
        match ensures("ret <= (!0 >> 1)") {
            Err(_) => {}
            Ok(p) => {
                assert!(
                    !smt::prove(p).is_proved(),
                    "`ret <= (!0 >> 1)` is `ret <= -1` in Rust and must never be proved"
                );
            }
        }
        // A typed operand fixes the sign, so the shift is exact and reads signed.
        // Check at several `x`, including `x == 0` where the bound is `-1`.
        let p = ensures("ret <= (!x >> 1)").expect("`!x >> 1` has a typed operand");
        for xv in [-128i16, -1, 0, 1, 127] {
            let x = xv as i8;
            let bound = (x as i64).wrapping_neg().wrapping_sub(1) >> 1;
            for rv in -128i16..=127 {
                let r = rv as i8;
                let got = smt::evaluate_pred(p, |i| match i {
                    0 => Some(x as u8 as u64),
                    1 => Some(r as u8 as u64),
                    _ => None,
                })
                .unwrap();
                let want = (r as i64) <= bound;
                assert_eq!(got, want, "`ret <= (!x >> 1)` read wrongly at x={x}, ret={r}");
            }
        }
    });
}

/// The refusal is narrow: shapes where signed and unsigned agree still read.
#[test]
fn ordinary_contracts_still_read() {
    smt::with_fresh(|| {
        for text in ["ret <= 5", "x >= -1", "ret == x + 1", "x & 7 == 0"] {
            ensures(text).unwrap_or_else(|e| panic!("`{text}` must still read: {}", e.reason));
        }
    });
}
