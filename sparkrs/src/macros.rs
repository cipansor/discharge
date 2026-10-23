//! Declarative macros that make verification read like syntax, the way
//! `Pre`/`Post`/`Assert` read in SPARK.
//!
//! Rust cannot literally add keywords, but it can add macros, and these are
//! deliberately shaped to feel like language constructs:
//!
//! ```
//! use sparkrs::prelude::*;
//! use sparkrs::sym::*;
//!
//! sparkrs::smt::with_fresh(|| {
//!     let x = var(8);
//!     // `verify!` discharges the predicate or fails loudly with the verdict.
//!     verify!(x.le_val(255));               // ∀ x:u8. x <= 255
//!     verify!((x & 0x0fu32).lt_val(16));     // ∀ x. x & 0x0f < 16
//!
//!     // `contract!` states pre/post and proves the implication.
//!     let v = contract! { requires x.lt_val(16), ensures x.lt_val(32) };
//!     assert!(v.is_proved());
//! });
//! ```
//!
//! `verify!` and `contract!` are *symbolic* (all inputs). `check!` is the
//! runtime counterpart on concrete values, so the same obligation can be
//! enforced in a deployed build where a proof was impossible or too expensive.

/// Discharge a predicate with the embedded decision procedure, panicking with
/// the full verdict (including any counterexample) if it is not proved.
#[macro_export]
macro_rules! verify {
    ($p:expr $(,)?) => {{
        let verdict = $crate::smt::prove($p);
        assert!(
            verdict.is_proved(),
            "sparkrs: verification obligation failed: {}",
            verdict
        );
        verdict
    }};
}

/// Prove `pre => post` and panic with the verdict if it does not hold.
#[macro_export]
macro_rules! verify_implies {
    ($pre:expr, $post:expr $(,)?) => {{
        let verdict = $crate::smt::prove_implies($pre, $post);
        assert!(
            verdict.is_proved(),
            "sparkrs: implication failed: {}",
            verdict
        );
        verdict
    }};
}

/// State a contract with SPARK-like syntax and discharge it.
///
/// ```ignore
/// let verdict = contract! {
///     requires x.le_val(1000),
///     ensures  x.lt_val(2000),
/// };
/// ```
#[macro_export]
macro_rules! contract {
    (requires $pre:expr, ensures $post:expr $(,)?) => {{
        $crate::vc::ensures($crate::vc::requires($pre), $post).discharge()
    }};
}

/// Produce a [`Certificate`](crate::proof::Certificate) for a predicate, or
/// panic if the prover could not establish it. The certificate is a value you
/// can pass around and compose, and its existence is what lets you build a
/// [`Verified`](crate::vc::Verified).
#[macro_export]
macro_rules! proof {
    ($p:expr $(,)?) => {{
        match $crate::proof::Certificate::discharge($p) {
            ::core::option::Option::Some(c) => c,
            ::core::option::Option::None => {
                panic!("sparkrs: could not prove the stated proposition")
            }
        }
    }};
}

/// A compile-time proof obligation: assert that a type-level proposition is
/// provable. If the kernel cannot build the proof term, this does not compile.
#[macro_export]
macro_rules! assert_proof {
    ($p:ty) => {{
        fn _sparkrs_assert_proof<T: $crate::proof::Theorem>() {}
        _sparkrs_assert_proof::<$p>();
    }};
}

/// Runtime check on a concrete value, mirroring `verify!`. Use this in the
/// deployed build for obligations that are checked, not proved.
#[macro_export]
macro_rules! check {
    ($p:expr, $value:expr $(,)?) => {{
        $crate::contract::assert_that($p, $value)
    }};
}

/// Complete proof by enumeration over a small domain.
///
/// ```ignore
/// // ∀ a b:u8. (a + b) wraps  <=>  result < a
/// verify_exhaustive!(a: u8, b: u8 => (a as u16 + b as u16 > 255) == (a.wrapping_add(b) < a));
/// ```
#[macro_export]
macro_rules! verify_exhaustive {
    ($a:ident : u8, $b:ident : u8 => $prop:expr $(,)?) => {{
        $crate::exhaustive::for_all_u8_2(|$a, $b| $prop)
    }};
    ($a:ident : u8 => $prop:expr $(,)?) => {{
        $crate::exhaustive::for_all_u8(|$a| $prop)
    }};
    ($a:ident : u16 => $prop:expr $(,)?) => {{
        $crate::exhaustive::for_all_u16(|$a| $prop)
    }};
}

#[cfg(test)]
mod tests {
    use crate::smt;
    use crate::smt::var;

    #[test]
    fn verify_macro_accepts_truths() {
        smt::with_fresh(|| {
            let x = var(8);
            verify!(x.lt_val(16).iff(x.lt_val(16)));
        });
    }

    #[test]
    #[should_panic(expected = "verification obligation failed")]
    fn verify_macro_rejects_falsehoods() {
        smt::with_fresh(|| {
            let x = var(8);
            verify!(x.lt_val(4));
        });
    }

    #[test]
    fn contract_macro_works() {
        smt::with_fresh(|| {
            let x = var(8);
            let v = contract! { requires x.lt_val(16), ensures x.lt_val(32) };
            assert!(v.is_proved());
        });
    }

    #[test]
    fn proof_macro_yields_a_certificate() {
        smt::with_fresh(|| {
            let x = var(8);
            let _c = proof!(x.lt_val(16).iff(x.lt_val(16)));
        });
    }

    #[test]
    fn exhaustive_macro_works() {
        // Wrapping addition overflows exactly when the result is below an operand.
        let ok = verify_exhaustive!(a: u8, b: u8 =>
            (a as u16 + b as u16 > 255) == (a.wrapping_add(b) < a));
        assert!(ok);
    }
}
