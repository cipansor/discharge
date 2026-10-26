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

/// Complete proof by enumeration over a small domain, panicking with the smallest
/// counterexample if the property does not hold.
///
/// ```ignore
/// // ∀ a b:u8. (a + b) wraps  <=>  result < a
/// verify_exhaustive!(a: u8, b: u8 => (a as u16 + b as u16 > 255) == (a.wrapping_add(b) < a));
/// ```
///
/// This used to *return* the boolean from `for_all_u8` and friends, so a false property
/// used as a statement — which is exactly how the example above reads, and how a reader
/// would naturally write it — was silently discarded and execution continued. Every
/// sibling macro in this module (`verify!`, `verify_implies!`, `contract!`, `proof!`)
/// panics on a failed obligation; a name that begins with `verify` must not be the one
/// that returns a value the caller can drop on the floor. The property is now discharged
/// by finding a violation and panicking with it, so the failure names the witness. Callers
/// who want the boolean call [`crate::exhaustive::for_all_u8`] and friends directly.
#[macro_export]
macro_rules! verify_exhaustive {
    ($a:ident : u8, $b:ident : u8 => $prop:expr $(,)?) => {{
        match $crate::exhaustive::find_violation_u8_2(|$a, $b| $prop) {
            ::core::option::Option::Some((a, b)) => panic!(
                "sparkrs: exhaustive verification failed: counterexample {} = {}, {} = {}",
                ::core::stringify!($a),
                a,
                ::core::stringify!($b),
                b
            ),
            ::core::option::Option::None => {}
        }
    }};
    ($a:ident : u8 => $prop:expr $(,)?) => {{
        match $crate::exhaustive::find_violation_u8(|$a| $prop) {
            ::core::option::Option::Some(a) => panic!(
                "sparkrs: exhaustive verification failed: counterexample {} = {}",
                ::core::stringify!($a),
                a
            ),
            ::core::option::Option::None => {}
        }
    }};
    ($a:ident : u16 => $prop:expr $(,)?) => {{
        match $crate::exhaustive::find_violation_u16(|$a| $prop) {
            ::core::option::Option::Some(a) => panic!(
                "sparkrs: exhaustive verification failed: counterexample {} = {}",
                ::core::stringify!($a),
                a
            ),
            ::core::option::Option::None => {}
        }
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
    fn check_macro_checks_concrete_values() {
        // `check!` is the runtime counterpart of `verify!`: the same predicate vocabulary
        // evaluated on one value, returning a structured error rather than panicking so it
        // can stay enabled in a deployed `no_std` build. It had no test, which is the one
        // macro in this module whose behaviour is observable at runtime rather than at
        // compile time.
        use crate::contract::{Obligation, Pred};
        assert!(check!(Pred::Lt(10), 9).is_ok());
        let err = check!(Pred::Lt(10), 10).unwrap_err();
        assert_eq!(err.kind, Obligation::Assertion);
        assert_eq!(err.value, 10);
    }

    #[test]
    fn exhaustive_macro_works() {
        // Wrapping addition overflows exactly when the result is below an operand.
        verify_exhaustive!(a: u8, b: u8 =>
            (a as u16 + b as u16 > 255) == (a.wrapping_add(b) < a));
        verify_exhaustive!(a: u8 => a.wrapping_add(0) == a);
    }

    #[test]
    #[should_panic(expected = "exhaustive verification failed: counterexample a = 128")]
    fn exhaustive_macro_rejects_falsehoods() {
        // The teeth for the fix: a false property must fail loudly, with the smallest
        // witness, rather than returning a boolean the caller can ignore. Before the fix
        // this ran to completion and printed nothing.
        verify_exhaustive!(a: u8 => a < 128);
    }
}
