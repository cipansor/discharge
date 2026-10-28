//! A symbolic DSL for writing specifications the way you write expressions.
//!
//! `smt` gives you functions; this module adds operator overloading so a
//! specification reads like the code it describes:
//!
//! ```
//! use discharge::prelude::*;
//! use discharge::sym::*;
//!
//! discharge::smt::with_fresh(|| {
//!     let x = var(32);
//!     let y = var(32);
//!     // ∀ x y. x + y == y + x
//!     assert!((x + y).eq(y + x).prove().is_proved());
//!     // ∀ x. x & 0xff < 256
//!     assert!((x & 0xffu32).lt_val(256).prove().is_proved());
//! });
//! ```
//!
//! Everything here is a thin, zero-cost wrapper over [`crate::smt`].

use crate::smt::{self, Pred, Var};
use core::ops::{Add, BitAnd, BitOr, BitXor, Mul, Not, Shl, Shr, Sub};

// --- word-shaped operators -------------------------------------------------

impl Add for Var {
    type Output = Var;
    fn add(self, rhs: Var) -> Var {
        smt::add(self, rhs)
    }
}

impl Sub for Var {
    type Output = Var;
    fn sub(self, rhs: Var) -> Var {
        smt::sub(self, rhs)
    }
}

impl Mul for Var {
    type Output = Var;
    fn mul(self, rhs: Var) -> Var {
        smt::mul(self, rhs)
    }
}

impl BitAnd for Var {
    type Output = Var;
    fn bitand(self, rhs: Var) -> Var {
        smt::band(self, rhs)
    }
}

impl BitOr for Var {
    type Output = Var;
    fn bitor(self, rhs: Var) -> Var {
        smt::bor(self, rhs)
    }
}

impl BitXor for Var {
    type Output = Var;
    fn bitxor(self, rhs: Var) -> Var {
        smt::bxor(self, rhs)
    }
}

impl Shl<u32> for Var {
    type Output = Var;
    fn shl(self, rhs: u32) -> Var {
        smt::shl(self, rhs)
    }
}

impl Shr<u32> for Var {
    type Output = Var;
    fn shr(self, rhs: u32) -> Var {
        smt::lshr(self, rhs)
    }
}

// `x & 0xff` should read as a mask, not require spelling out `word(0xff, 32)`.
// Both `u32` and `u64` literals are accepted because Rust will infer either
// depending on how the specification is written.
//
// The set of operators here has to be *complete*, not merely the convenient ones. It
// originally covered `+`, `*`, `&` and `|` but not `-` or `^`, so `x - 1u32` and
// `x ^ 0xffu32` were compile errors while `x + 1u32` and `x & 0xffu32` were fine. A user
// cannot predict which literal operations exist from the ones that do, and the DSL's whole
// claim is that a specification reads like the expression it describes. Subtraction and
// XOR by a constant are as natural as addition and AND, so all six are provided.
macro_rules! impl_word_literal_ops {
    ($($t:ty),*) => {$(
        impl BitAnd<$t> for Var {
            type Output = Var;
            fn bitand(self, rhs: $t) -> Var {
                smt::band(self, smt::word(rhs as u64, smt::bits(self)))
            }
        }

        impl BitOr<$t> for Var {
            type Output = Var;
            fn bitor(self, rhs: $t) -> Var {
                smt::bor(self, smt::word(rhs as u64, smt::bits(self)))
            }
        }

        impl BitXor<$t> for Var {
            type Output = Var;
            fn bitxor(self, rhs: $t) -> Var {
                smt::bxor(self, smt::word(rhs as u64, smt::bits(self)))
            }
        }

        impl Add<$t> for Var {
            type Output = Var;
            fn add(self, rhs: $t) -> Var {
                smt::add(self, smt::word(rhs as u64, smt::bits(self)))
            }
        }

        impl Sub<$t> for Var {
            type Output = Var;
            fn sub(self, rhs: $t) -> Var {
                smt::sub(self, smt::word(rhs as u64, smt::bits(self)))
            }
        }

        impl Mul<$t> for Var {
            type Output = Var;
            fn mul(self, rhs: $t) -> Var {
                smt::mul(self, smt::word(rhs as u64, smt::bits(self)))
            }
        }
    )*};
}

impl_word_literal_ops!(u32, u64);

// --- predicates ------------------------------------------------------------

impl Not for Pred {
    type Output = Pred;
    fn not(self) -> Pred {
        smt::not(self)
    }
}

impl BitAnd for Pred {
    type Output = Pred;
    fn bitand(self, rhs: Pred) -> Pred {
        smt::and(self, rhs)
    }
}

impl BitOr for Pred {
    type Output = Pred;
    fn bitor(self, rhs: Pred) -> Pred {
        smt::or(self, rhs)
    }
}

impl BitXor for Pred {
    type Output = Pred;
    fn bitxor(self, rhs: Pred) -> Pred {
        smt::xor(self, rhs)
    }
}

impl Pred {
    /// `self => other`
    pub fn implies(self, other: Pred) -> Pred {
        smt::implies(self, other)
    }
    /// `self <=> other`
    pub fn iff(self, other: Pred) -> Pred {
        smt::iff(self, other)
    }
    /// Discharge this predicate with the embedded decision procedure.
    pub fn prove(self) -> smt::Verdict {
        smt::prove(self)
    }
    /// Search for a model of this predicate.
    pub fn find_model(self) -> smt::Verdict {
        smt::find_model(self)
    }
}

impl Var {
    /// Width of this symbolic word, in bits.
    pub fn width(self) -> u8 {
        smt::bits(self)
    }

    /// The variable's index, as reported in counterexamples.
    pub fn index(self) -> u32 {
        smt::index(self)
    }
    /// `self == other`
    pub fn eq(self, other: Var) -> Pred {
        smt::eq(self, other)
    }
    /// `self == k`
    pub fn eq_val(self, k: u64) -> Pred {
        smt::eq_const(self, k)
    }
    /// `self != other`
    pub fn ne(self, other: Var) -> Pred {
        smt::not(smt::eq(self, other))
    }
    /// `self < other` (unsigned)
    pub fn lt(self, other: Var) -> Pred {
        smt::ult(self, other)
    }
    /// `self <= other` (unsigned)
    pub fn le(self, other: Var) -> Pred {
        smt::ule(self, other)
    }
    /// `self >= other` (unsigned)
    pub fn ge(self, other: Var) -> Pred {
        smt::ule(other, self)
    }
    /// `self > other` (unsigned)
    pub fn gt(self, other: Var) -> Pred {
        smt::ult(other, self)
    }
    /// `self < k`
    pub fn lt_val(self, k: u64) -> Pred {
        smt::ult_const(self, k)
    }
    /// `self <= k`
    pub fn le_val(self, k: u64) -> Pred {
        smt::ule_const(self, k)
    }
    /// `self >= k`
    pub fn ge_val(self, k: u64) -> Pred {
        smt::uge_const(self, k)
    }
    /// `self > k`
    pub fn gt_val(self, k: u64) -> Pred {
        smt::ugt_const(self, k)
    }
}

/// Universal quantification is implicit: a `Pred` over symbolic variables is a
/// statement about *all* values. This alias documents intent at call sites.
pub fn forall(p: Pred) -> Pred {
    p
}
