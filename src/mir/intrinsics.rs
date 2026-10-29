//! The `core::num` operations the frontend models instead of treating as unknown.
//!
//! A call the frontend cannot model makes the whole *path* unknown, and the
//! `checked_*`, `saturating_*` and `wrapping_*` families are how real Rust
//! writes arithmetic that must not panic. They are also the easiest calls to
//! model exactly: each is a pure function of its arguments with a definition
//! that fits in a line.
//!
//! The default everywhere else is to refuse an unmodelled call rather than
//! approximate it, and that stays true here -- a name not in the tables below is
//! not modelled, and a name that *is* listed but whose shape does not match is
//! also not modelled. What changes is that the three families below have a
//! definition, and the definition is used.
//!
//! # What is modelled, and why the result is not a guess
//!
//! * `wrapping_*` — the operation with the result taken modulo `2^w`. That is
//!   exactly what MIR's plain `Add`/`Sub`/`Mul`/`BitAnd`/… already compute, so
//!   the wrapping model is the *same term* a plain operator produces rather than
//!   a second definition that could drift from it.
//! * `saturating_*` — the operation, clamped. The clamp is `if it would overflow
//!   { bound } else { result }`, and the overflow test is the one rustc's own
//!   `assert` reads, so a function written with `saturating_add` and one written
//!   with a hand-rolled guard are decided by one rule.
//! * `checked_*` — an `Option<T>`. The tag is the *negation* of the overflow
//!   test and the payload is the result, so `Some` means exactly "defined".
//! * `count_ones` — a sum of the operand's bits, at the *return* type's width.
//!   It is the one modelled call whose result is wider than its operand
//!   (`u8::count_ones` returns `u32`), so the count is built at the operand's
//!   width and zero-extended, which is the promotion Rust performs.
//! * `wrapping_abs` — `if x < 0 { 0 - x } else { x }`. The `0 - x` wraps at
//!   `MIN`, where the magnitude is unrepresentable, and that wrap *is* the
//!   method's answer, so the expression is the whole definition rather than a
//!   near miss that needs a special case for `MIN`.
//!
//! # What is not, and why refusing is the right answer
//!
//! * `saturating_div`, `wrapping_div` and the rest of the division family panic
//!   on a zero divisor. Modelling them as total would *hide a panic*, which is
//!   the one thing this frontend must never do, so only `checked_div` (which
//!   returns `None` instead) is modelled, and only up to [`DIV_MAX_WIDTH`].
//! * The shifts are refused because the families disagree: `wrapping_shl` takes
//!   the amount modulo the width, while the engine's variable shift saturates to
//!   zero, and `checked_shl` returns `None` past the width. Three behaviours
//!   under one name is not something to guess at.
//! * `unchecked_*` is undefined behaviour on overflow. There is no value to
//!   model, and a proof about UB is not a proof, so it is refused.
//! * `pow`, `neg`, `add_signed`, the float ops, `rotate_*`, the zero-counts
//!   (`leading_zeros`, `trailing_zeros`, `count_zeros`) and the `is_*`
//!   predicates are absent, so they keep the refusal they had. `pow` and `neg`
//!   are *reachable* extensions -- `pow(x, k)` is a `k`-fold product and
//!   `wrapping_neg` is `0 - x` -- but neither is modelled yet, and an
//!   unmodelled name is refused rather than approximated.

use crate::mir::parse::BinOp;
use crate::smt::{self, Pred, Var};

/// The widest bit-vector the divider is asked about.
///
/// The engine's divider is exact but large, and a quotient term at `u64` is past
/// what the BDD holds. Above this the model declines, which leaves the path
/// unknown rather than slow. Declining is the intended answer; a model that
/// hangs is worse than one that says "I could not decide".
pub const DIV_MAX_WIDTH: u8 = 32;

/// The widest operand whose *product* the model will widen to test.
///
/// Overflow for a product needs the exact `2w`-bit result, and a `2w`-bit
/// multiplier is the scaling wall this crate documents. Past this the query is
/// not worth posing, so the model declines and the path stays unknown. This is
/// the same wall the plain `*` path hits; the bound is stated here so the two
/// cannot drift.
pub const MUL_MAX_WIDTH: u8 = 8;

/// The discriminant of the `Some` variant, where a modelled `Option` payload
/// lives. rustc numbers `None` 0 and `Some` 1.
pub const SOME_TAG: u64 = 1;

/// What a modelled intrinsic computes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Intrinsic {
    /// The operation, result taken modulo `2^w`. Cannot fail.
    Wrapping(BinOp),
    /// The operation, clamped to the type's range. Cannot fail.
    Saturating(BinOp),
    /// The operation as `Option<T>`: `None` where it would overflow or divide by
    /// zero, `Some(result)` otherwise.
    Checked(BinOp),
    /// The number of set bits, as a value of the *return* type (which is wider
    /// than the operand: `u8::count_ones` returns `u32`). Cannot fail.
    ///
    /// It is not a [`BinOp`] family member because it is not an operator at all:
    /// the `wrapping_`/`saturating_`/`checked_` prefix that names the other
    /// families does not apply, and neither does the two-operand shape.
    Popcount,
    /// The absolute value, taken modulo `2^w` (`wrapping_abs`). Cannot fail.
    ///
    /// Like [`Intrinsic::Popcount`] it has no family prefix, and it is unary.
    /// The result width equals the operand width, and the two disagree about
    /// nothing except the `MIN` case, where the magnitude is unrepresentable and
    /// the wrapped value is `MIN` itself.
    Abs,
}

impl Intrinsic {
    /// True for the two shapes that take one operand and no operator.
    ///
    /// `eval` and the executor both branch on this: a unary call has no second
    /// argument to read, so the two-operand path must not be entered for it.
    pub fn is_unary(self) -> bool {
        matches!(self, Intrinsic::Popcount | Intrinsic::Abs)
    }
}

/// What a modelled call produced.
#[derive(Clone, Copy, Debug)]
pub enum Outcome {
    /// A plain value, written to the destination local.
    Value(Var),
    /// An `Option`. The tag is a *term*, not a constant: it is `1` where the
    /// operation is defined and `0` where it is not, so the `switchInt` that
    /// consumes it takes the right arm on each path. The payload is the
    /// operation's result, and it is only ever read on a path whose condition
    /// already forces the tag to `Some` -- rustc emits the downcast projection
    /// only inside that arm, which is what makes an ungated payload sound.
    Option { tag: Var, payload: Var },
}

/// The family a `core::num` method name belongs to, if any.
///
/// The name is matched after the last `::`, so both `core::num::<impl
/// u8>::checked_add` and a bare `checked_add` resolve. The whole suffix is
/// matched, not a prefix of it, so `wrapping_add_signed` and `saturating_pow`
/// are refused rather than read as `wrapping_add` and `saturating_add`.
///
/// Two shapes are not families at all and are matched before the prefix split:
/// `count_ones` and `wrapping_abs`. `count_ones` has no `wrapping_`/`saturating_`
/// /`checked_` prefix and no sibling that this crate models, and `wrapping_abs`
/// would otherwise be read as `wrapping_` + an operator named `abs`, which is not
/// in the operator table. Matching them first keeps the family split honest: it
/// only ever sees an operator name.
pub fn classify(name: &str) -> Option<Intrinsic> {
    let short = name.rsplit("::").next().unwrap_or(name);
    if short == "count_ones" {
        return Some(Intrinsic::Popcount);
    }
    if short == "wrapping_abs" {
        return Some(Intrinsic::Abs);
    }
    let (family, op) = if let Some(rest) = short.strip_prefix("wrapping_") {
        (0u8, rest)
    } else if let Some(rest) = short.strip_prefix("saturating_") {
        (1u8, rest)
    } else {
        (2u8, short.strip_prefix("checked_")?)
    };
    let op = match op {
        "add" => BinOp::Add,
        "sub" => BinOp::Sub,
        "mul" => BinOp::Mul,
        "and" => BinOp::BitAnd,
        "or" => BinOp::BitOr,
        "xor" => BinOp::BitXor,
        // Only `checked_div`/`checked_rem` are total; the others panic on a zero
        // divisor and are refused by `is_modelled`.
        "div" => BinOp::Div,
        "rem" => BinOp::Rem,
        _ => return None,
    };
    Some(match family {
        0 => Intrinsic::Wrapping(op),
        1 => Intrinsic::Saturating(op),
        _ => Intrinsic::Checked(op),
    })
}

/// Whether the model has a definition for this operation at this width.
///
/// `w` is the *operand* width, not the return type's: `checked_add` on a `u8`
/// returns `Option<u8>` but overflows at 8 bits. `signed` decides what overflow
/// means and where the saturating bounds sit.
pub fn is_modelled(op: Intrinsic, w: u8, signed: bool) -> bool {
    let _ = signed;
    if w == 0 || w > 64 {
        return false;
    }
    match op {
        // `count_ones` is a sum of the operand's bits, so it is exact at any
        // width the engine holds. Its *result* is `u32` for any operand up to
        // `u32`, and the model builds it by zero-extending the count to that
        // width -- so `w` here is the operand width, and the result width is
        // whatever the caller's destination type says.
        Intrinsic::Popcount => true,
        // `wrapping_abs` is `if x < 0 { -x } else { x }` modulo `2^w`, which is
        // defined at every width. The signed reading is what makes the sign
        // bit meaningful; on an unsigned type the method does not exist, so a
        // dump that calls it was signed.
        Intrinsic::Abs => true,
        // The two-operand families. `binop` is `Some` for exactly these.
        Intrinsic::Wrapping(bin)
        | Intrinsic::Saturating(bin)
        | Intrinsic::Checked(bin) => match bin {
            // Division is only modelled for the family that can express the
            // failure as a value rather than a panic.
            BinOp::Div | BinOp::Rem => matches!(op, Intrinsic::Checked(_)) && w <= DIV_MAX_WIDTH,
            // A product needs the widened exact result to test, and to clamp.
            BinOp::Mul => w <= MUL_MAX_WIDTH,
            BinOp::Add | BinOp::Sub | BinOp::BitAnd | BinOp::BitOr | BinOp::BitXor => true,
            BinOp::Shl | BinOp::Shr | BinOp::Eq | BinOp::Ne | BinOp::Lt | BinOp::Le | BinOp::Gt
            | BinOp::Ge => false,
        },
    }
}

/// The value a modelled call yields.
///
/// A mismatch -- a width the engine cannot hold, a shape with no definition --
/// returns `None`, and the caller reports the path as unknown rather than
/// guessing.
///
/// `w` is the operand width. `result_w` is the destination type's width, which
/// differs from `w` only for `count_ones` (`u8::count_ones` returns `u32`); for
/// every other shape the two are equal, and the caller passes `w` for both. The
/// result term is built at `result_w` so that it has the width of the local it is
/// written to -- a term narrower than its local would make the next read of that
/// local ill-formed.
pub fn eval(op: Intrinsic, x: Var, y: Var, w: u8, signed: bool, result_w: u8) -> Option<Outcome> {
    if !is_modelled(op, w, signed) || result_w == 0 || result_w > 64 {
        return None;
    }
    Some(match op {
        // The bit count, widened to the result type. `popcount` returns a term of
        // the operand's width, which is wide enough because the count cannot
        // exceed the operand width; zero-extending it to `result_w` is the
        // promotion Rust performs. For a `u32` result of a `u8` operand that is
        // an 8- to 32-bit widening, and for the (signed) fixed-width case where
        // `w == result_w` it is a no-op.
        Intrinsic::Popcount => Outcome::Value(smt::truncate(popcount(x), result_w)),
        // `wrapping_abs`: the magnitude, except at `MIN` where the magnitude is
        // not representable and the wrapped result is `MIN` itself. Written as
        // `if x < 0 { 0 - x } else { x }`, which already yields `MIN` at `MIN`
        // because `0 - MIN` wraps -- so no separate `MIN` case is needed, and
        // stating one would be a second definition that could drift.
        Intrinsic::Abs => Outcome::Value(smt::ite(smt::negative(x), smt::sub(smt::word(0, w), x), x)),
        Intrinsic::Wrapping(bin) => {
            let plain = plain_result(bin, x, y, signed)?;
            Outcome::Value(smt::truncate(plain, result_w))
        }
        Intrinsic::Saturating(bin) => {
            let plain = plain_result(bin, x, y, signed)?;
            let bound = saturation_bound(bin, x, y, w, signed)?;
            let fails = failure(bin, x, y, w, signed)?;
            Outcome::Value(smt::truncate(smt::ite(fails, bound, plain), result_w))
        }
        Intrinsic::Checked(bin) => {
            let plain = plain_result(bin, x, y, signed)?;
            let fails = failure(bin, x, y, w, signed)?;
            // The tag is `1` exactly where the operation is defined, so the
            // `switchInt` on it takes the `Some` arm on those paths and the
            // `None` arm on the rest. It is a term, not a constant, and it is
            // what lets the payload be recorded unconditionally: rustc only
            // reads the payload inside the `Some` arm, where this tag is `1`.
            Outcome::Option {
                tag: smt::ite(fails, smt::word(0, w), smt::word(1, w)),
                payload: smt::truncate(plain, result_w),
            }
        }
    })
}

/// The number of set bits in `x`, as a term of the *same width* as `x`.
///
/// A tree of adds over the individual bits: `x & 1` is bit 0, `(x >> k) & 1` is
/// bit `k`, and the sum of those is the count. The bits are extracted as
/// predicates rather than as one-bit terms because `smt` has no one-bit word to
/// add, and `ite(bit, 1, 0)` turns each into a term the adder already handles.
///
/// The width is the operand's, not the result type's: a `u8` count never exceeds
/// 8, so 8 bits hold it, and the caller widens to the destination type. Building
/// it wide here would add terms the zero-extension throws away.
fn popcount(x: Var) -> Var {
    let w = smt::bits(x);
    let mut acc = smt::word(0, w);
    let one = smt::word(1, w);
    for k in 0..w {
        // The `k`-th bit, as `1` or `0`.
        let bit = smt::ite(smt::eq_const(smt::band(smt::lshr(x, k as u32), one), 1), one, smt::word(0, w));
        acc = smt::add(acc, bit);
    }
    acc
}

/// The operation with the result taken modulo `2^w`.
///
/// For `+`, `-`, `*` and the bitwise ops this is MIR's plain operator, so the
/// term is the same one a hand-written `a + b` produces. Division and remainder
/// go through the engine's restoring divider, which is exact for a non-zero
/// divisor; the zero-divisor case is defined there too, and it is the failure
/// predicate that stops that value from ever being used as a result.
fn plain_result(op: BinOp, x: Var, y: Var, signed: bool) -> Option<Var> {
    Some(match op {
        BinOp::Add => smt::add(x, y),
        BinOp::Sub => smt::sub(x, y),
        BinOp::Mul => smt::mul(x, y),
        BinOp::BitAnd => smt::band(x, y),
        BinOp::BitOr => smt::bor(x, y),
        BinOp::BitXor => smt::bxor(x, y),
        // A signed operand needs the *signed* divider: the unsigned one returns
        // a huge positive quotient for `-7 / 2`, which is a wrong value and not
        // merely a weaker proof.
        BinOp::Div if signed => smt::sdiv(x, y),
        BinOp::Rem if signed => smt::srem(x, y),
        BinOp::Div => smt::udiv(x, y),
        BinOp::Rem => smt::urem(x, y),
        _ => return None,
    })
}

/// The condition under which the operation is not the plain result.
///
/// This is the predicate rustc's `assert` reads, which is what makes a
/// `saturating_*` and a hand-rolled overflow guard agree.
fn failure(op: BinOp, x: Var, y: Var, w: u8, signed: bool) -> Option<Pred> {
    Some(match op {
        // Unsigned addition wraps exactly when the sum is below `x` — the carry
        // out of the top bit, which the unsigned order tracks.
        //
        // Signed addition is a different condition, and getting it wrong is
        // unsound rather than merely weak: `-1 + 1` does not overflow but its sum
        // is below `127` read unsigned, so the unsigned test fires on it. The
        // sign rule has no such cases — the result is wrong exactly when the
        // operands agree in sign and the result disagrees with them.
        BinOp::Add if signed => {
            let sum = smt::add(x, y);
            smt::and(
                smt::iff(smt::negative(x), smt::negative(y)),
                smt::xor(smt::negative(x), smt::negative(sum)),
            )
        }
        BinOp::Add => smt::ult(smt::add(x, y), x),
        // Unsigned subtraction wraps exactly when `x < y` (the borrow).
        BinOp::Sub if signed => {
            let diff = smt::sub(x, y);
            smt::and(
                smt::xor(smt::negative(x), smt::negative(y)),
                smt::iff(smt::negative(y), smt::negative(diff)),
            )
        }
        BinOp::Sub => smt::ult(x, y),
        // A product wraps exactly when the exact result needs more than `w` bits.
        // The exact result is built by widening: `truncate` zero-extends when the
        // target is wider, so the operands are widened to `2w` and multiplied
        // exactly there. Exact rather than a sufficient condition, because a
        // too-weak predicate would make an overflowing function look panic-free.
        BinOp::Mul => {
            let wide = w.saturating_mul(2).min(64);
            if wide <= w || wide > 16 {
                return None;
            }
            if signed {
                // The `2w`-bit product of two `w`-bit signed values always fits
                // in `2w` signed bits, so this multiply cannot itself wrap. The
                // result is right exactly when it equals the `w`-bit wrapped
                // result sign-extended back to `2w`; comparing a *zero*-extended
                // result would fire on every negative product.
                let exact = smt::mul(smt::sign_extend(x, wide), smt::sign_extend(y, wide));
                let want = smt::sign_extend(smt::mul(x, y), wide);
                smt::not(smt::eq(exact, want))
            } else {
                let exact = smt::mul(smt::truncate(x, wide), smt::truncate(y, wide));
                // 2^w, as a constant in the widened width.
                let limit = 1u64 << (w - 1);
                let limit = limit.saturating_mul(2);
                smt::uge_const(exact, limit)
            }
        }
        // Division and remainder fail on a zero divisor. The signed forms fail
        // on `MIN / -1` as well: the quotient is not representable, and
        // `checked_div` returns `None` there rather than wrapping.
        BinOp::Div | BinOp::Rem if signed => {
            let min = min_value(w)?;
            let zero_divisor = smt::eq_const(y, 0);
            let min_by_neg_one =
                smt::and(smt::eq_const(x, min), smt::eq_const(y, all_ones_value(w)));
            smt::or(zero_divisor, min_by_neg_one)
        }
        BinOp::Div | BinOp::Rem => smt::eq_const(y, 0),
        _ => return None,
    })
}

/// The value a saturating operation takes when it would overflow.
///
/// The direction is the sign of the *overflow*, not of the operator, and that
/// distinction is the whole content of the function. An unsigned `a - b` with
/// `a < b` saturates to zero, while a signed `a - b` with `a >= 0, b < 0`
/// saturates to the maximum: same operator, opposite ends.
fn saturation_bound(op: BinOp, x: Var, y: Var, w: u8, signed: bool) -> Option<Var> {
    let (lo, hi) = bounds(w, signed)?;
    Some(match op {
        // Unsigned addition and multiplication only ever overflow upward.
        BinOp::Add | BinOp::Mul if !signed => hi,
        // Unsigned subtraction only ever borrows downward.
        BinOp::Sub if !signed => lo,
        // Signed addition overflows only when the operands agree in sign, and
        // then the true sum takes that sign -- so the operand's sign is the
        // direction.
        BinOp::Add => smt::ite(smt::negative(x), lo, hi),
        // Signed subtraction overflows only when the operands differ, and then
        // the true difference takes the sign of `x`, not of `y`.
        BinOp::Sub => smt::ite(smt::negative(x), lo, hi),
        // Signed multiplication overflows upward when the operands agree in sign
        // and downward when they differ.
        BinOp::Mul => smt::ite(smt::xor(smt::negative(x), smt::negative(y)), lo, hi),
        _ => return None,
    })
}

/// The minimum and maximum of a `w`-bit integer, as constants.
fn bounds(w: u8, signed: bool) -> Option<(Var, Var)> {
    let max = max_value(w)?;
    if signed {
        Some((smt::word(min_value(w)?, w), smt::word(max >> 1, w)))
    } else {
        Some((smt::word(0, w), smt::word(max, w)))
    }
}

/// `2^w - 1`, the unsigned maximum.
fn max_value(w: u8) -> Option<u64> {
    if w == 0 || w > 64 {
        return None;
    }
    Some(if w == 64 { u64::MAX } else { (1u64 << w) - 1 })
}

/// `-2^(w-1)`, the signed minimum, as its two's-complement bit pattern.
fn min_value(w: u8) -> Option<u64> {
    if w == 0 || w > 64 {
        return None;
    }
    Some(1u64 << (w - 1))
}

/// `-1` as a `w`-bit two's-complement word.
fn all_ones_value(w: u8) -> u64 {
    max_value(w).unwrap_or(0)
}

#[cfg(test)]
mod tests {
    //! Differential test: the model against `core`'s own arithmetic.
    //!
    //! The model here is only useful if it agrees with the real `checked_*`,
    //! `saturating_*` and `wrapping_*` on *every* input, not on the inputs that
    //! happened to be tried. So each case is compared against the `core` call
    //! itself, over all of `u8` and all of `i8` -- small enough to enumerate in
    //! full, and the widths where every sign and boundary rule bites.
    //!
    //! This lives as a unit test rather than under `tests/` because the model is
    //! crate-internal, which is the same reason the IR checks live beside the IR.
    //!
    //! Each operation's term is built once and evaluated per input pair, so the
    //! full cross product is a walk over a fixed term rather than an arena reset
    //! per pair.

    use super::*;

    /// Walk every pair of `w`-bit inputs, calling `f(x, y)` for each.
    fn each_pair(w: u8, mut f: impl FnMut(u64, u64)) {
        let n = 1u64 << w;
        for x in 0..n {
            for y in 0..n {
                f(x, y);
            }
        }
    }

    /// The concrete meaning of an outcome under one input pair.
    ///
    /// The outcome holds *terms*; `smt::evaluate` turns "the model computed
    /// this" into "the model computed this value", which is what can be compared
    /// against Rust.
    fn read(outcome: Outcome, ai: u32, bi: u32, x: u64, y: u64) -> (Option<bool>, Option<u64>) {
        let env = |i: u32| {
            if i == ai {
                Some(x)
            } else if i == bi {
                Some(y)
            } else {
                None
            }
        };
        match outcome {
            Outcome::Value(v) => (None, smt::evaluate(v, env)),
            Outcome::Option { tag, payload } => {
                (smt::evaluate(tag, env).map(|t| t != 0), smt::evaluate(payload, env))
            }
        }
    }

    /// Build `op`'s term once, then check every input pair against `rust`.
    ///
    /// `rust` answers with the `core` result for a pair: `Some(v)` when the
    /// operation is defined, `None` when `checked_*` would return `None`. A
    /// saturating or wrapping operation always answers `Some`, which is the point
    /// -- those never fail. `from_bits`/`to_bits` reinterpret the bit pattern as
    /// the signed type for the oracle and back.
    fn check(
        op: Intrinsic,
        w: u8,
        signed: bool,
        from_bits: impl Fn(u64) -> i64,
        to_bits: impl Fn(i64) -> u64,
        rust: impl Fn(i64, i64) -> Option<i64>,
        label: &str,
    ) {
        smt::with_fresh(|| {
            let a = smt::var(w);
            let b = smt::var(w);
            let outcome = eval(op, a, b, w, signed, w)
                .unwrap_or_else(|| panic!("{label} at {w} bits must be modelled"));
            let (ai, bi) = (smt::index(a), smt::index(b));
            each_pair(w, |xb, yb| {
                let (x, y) = (from_bits(xb), from_bits(yb));
                let want = rust(x, y);
                let (got_some, got_val) = read(outcome, ai, bi, xb, yb);
                match (got_some, want) {
                    // An `Option` outcome, checked against a `checked_*`.
                    (Some(true), Some(r)) => assert_eq!(
                        got_val,
                        Some(to_bits(r)),
                        "{label} at ({x}, {y}): the model says {got_val:?}, Rust says {r}"
                    ),
                    (Some(true), None) => panic!(
                        "{label} at ({x}, {y}): the model says `Some`, Rust says `None`"
                    ),
                    (Some(false), Some(r)) => panic!(
                        "{label} at ({x}, {y}): the model says `None`, Rust says `{r}`"
                    ),
                    (Some(false), None) => {}
                    // A plain value, checked against a total operation.
                    (None, Some(r)) => assert_eq!(
                        got_val,
                        Some(to_bits(r)),
                        "{label} at ({x}, {y}): the model says {got_val:?}, Rust says {r}"
                    ),
                    (None, None) => panic!("{label}: a plain outcome cannot match a failing oracle"),
                }
            });
        });
    }

    /// The unsigned reinterpretations: a bit pattern is the value, both ways.
    fn ident(v: i64) -> u64 {
        v as u64
    }

    fn unident(bits: u64) -> i64 {
        bits as i64
    }

    #[test]
    fn checked_u8_agrees_with_rust() {
        check(
            Intrinsic::Checked(BinOp::Add),
            8,
            false,
            unident,
            ident,
            |x, y| u8::checked_add(x as u8, y as u8).map(|v| v as i64),
            "checked_add u8",
        );
        check(
            Intrinsic::Checked(BinOp::Sub),
            8,
            false,
            unident,
            ident,
            |x, y| u8::checked_sub(x as u8, y as u8).map(|v| v as i64),
            "checked_sub u8",
        );
        check(
            Intrinsic::Checked(BinOp::Mul),
            8,
            false,
            unident,
            ident,
            |x, y| u8::checked_mul(x as u8, y as u8).map(|v| v as i64),
            "checked_mul u8",
        );
    }

    #[test]
    fn saturating_u8_agrees_with_rust() {
        check(
            Intrinsic::Saturating(BinOp::Add),
            8,
            false,
            unident,
            ident,
            |x, y| Some(u8::saturating_add(x as u8, y as u8) as i64),
            "saturating_add u8",
        );
        check(
            Intrinsic::Saturating(BinOp::Sub),
            8,
            false,
            unident,
            ident,
            |x, y| Some(u8::saturating_sub(x as u8, y as u8) as i64),
            "saturating_sub u8",
        );
        check(
            Intrinsic::Saturating(BinOp::Mul),
            8,
            false,
            unident,
            ident,
            |x, y| Some(u8::saturating_mul(x as u8, y as u8) as i64),
            "saturating_mul u8",
        );
    }

    #[test]
    fn wrapping_u8_agrees_with_rust() {
        check(
            Intrinsic::Wrapping(BinOp::Add),
            8,
            false,
            unident,
            ident,
            |x, y| Some(u8::wrapping_add(x as u8, y as u8) as i64),
            "wrapping_add u8",
        );
        check(
            Intrinsic::Wrapping(BinOp::Sub),
            8,
            false,
            unident,
            ident,
            |x, y| Some(u8::wrapping_sub(x as u8, y as u8) as i64),
            "wrapping_sub u8",
        );
        check(
            Intrinsic::Wrapping(BinOp::Mul),
            8,
            false,
            unident,
            ident,
            |x, y| Some(u8::wrapping_mul(x as u8, y as u8) as i64),
            "wrapping_mul u8",
        );
    }

    #[test]
    fn checked_div_and_rem_agree_with_rust() {
        check(
            Intrinsic::Checked(BinOp::Div),
            8,
            false,
            unident,
            ident,
            |x, y| u8::checked_div(x as u8, y as u8).map(|v| v as i64),
            "checked_div u8",
        );
        check(
            Intrinsic::Checked(BinOp::Rem),
            8,
            false,
            unident,
            ident,
            |x, y| u8::checked_rem(x as u8, y as u8).map(|v| v as i64),
            "checked_rem u8",
        );
    }

    /// Reinterpret a two's-complement bit pattern as `i8`, for the signed oracle.
    fn to_i8(bits: u64) -> i64 {
        (bits as u8) as i8 as i64
    }

    /// The inverse, for comparing an `i8` result against the model's bits.
    fn i8_bits(v: i64) -> u64 {
        (v as i8) as u8 as u64
    }

    #[test]
    fn checked_i8_agrees_with_rust() {
        check(
            Intrinsic::Checked(BinOp::Add),
            8,
            true,
            to_i8,
            i8_bits,
            |x, y| i8::checked_add(x as i8, y as i8).map(|v| v as i64),
            "checked_add i8",
        );
        check(
            Intrinsic::Checked(BinOp::Sub),
            8,
            true,
            to_i8,
            i8_bits,
            |x, y| i8::checked_sub(x as i8, y as i8).map(|v| v as i64),
            "checked_sub i8",
        );
        check(
            Intrinsic::Checked(BinOp::Mul),
            8,
            true,
            to_i8,
            i8_bits,
            |x, y| i8::checked_mul(x as i8, y as i8).map(|v| v as i64),
            "checked_mul i8",
        );
        check(
            Intrinsic::Checked(BinOp::Div),
            8,
            true,
            to_i8,
            i8_bits,
            |x, y| i8::checked_div(x as i8, y as i8).map(|v| v as i64),
            "checked_div i8",
        );
        check(
            Intrinsic::Checked(BinOp::Rem),
            8,
            true,
            to_i8,
            i8_bits,
            |x, y| i8::checked_rem(x as i8, y as i8).map(|v| v as i64),
            "checked_rem i8",
        );
    }

    #[test]
    fn saturating_and_wrapping_i8_agree_with_rust() {
        check(
            Intrinsic::Saturating(BinOp::Add),
            8,
            true,
            to_i8,
            i8_bits,
            |x, y| Some(i8::saturating_add(x as i8, y as i8) as i64),
            "saturating_add i8",
        );
        check(
            Intrinsic::Saturating(BinOp::Sub),
            8,
            true,
            to_i8,
            i8_bits,
            |x, y| Some(i8::saturating_sub(x as i8, y as i8) as i64),
            "saturating_sub i8",
        );
        check(
            Intrinsic::Saturating(BinOp::Mul),
            8,
            true,
            to_i8,
            i8_bits,
            |x, y| Some(i8::saturating_mul(x as i8, y as i8) as i64),
            "saturating_mul i8",
        );
        check(
            Intrinsic::Wrapping(BinOp::Add),
            8,
            true,
            to_i8,
            i8_bits,
            |x, y| Some(i8::wrapping_add(x as i8, y as i8) as i64),
            "wrapping_add i8",
        );
        check(
            Intrinsic::Wrapping(BinOp::Sub),
            8,
            true,
            to_i8,
            i8_bits,
            |x, y| Some(i8::wrapping_sub(x as i8, y as i8) as i64),
            "wrapping_sub i8",
        );
        check(
            Intrinsic::Wrapping(BinOp::Mul),
            8,
            true,
            to_i8,
            i8_bits,
            |x, y| Some(i8::wrapping_mul(x as i8, y as i8) as i64),
            "wrapping_mul i8",
        );
    }

    /// `u16`, so the width-dependence of the overflow test is exercised at a
    /// second width rather than only at 8 bits. The full `u16` cross product is
    /// 2^32, so this samples the boundaries plus a spread of interior values.
    #[test]
    fn saturating_u16_agrees_with_rust_at_the_boundaries() {
        let vals: [u16; 12] = [0, 1, 2, 15, 100, 255, 256, 32767, 32768, 65534, 65535, 12345];
        smt::with_fresh(|| {
            let a = smt::var(16);
            let b = smt::var(16);
            let op = Intrinsic::Saturating(BinOp::Add);
            let outcome = eval(op, a, b, 16, false, 16).expect("u16 is modelled");
            let (ai, bi) = (smt::index(a), smt::index(b));
            for &x in &vals {
                for &y in &vals {
                    let (_, got) = read(outcome, ai, bi, x as u64, y as u64);
                    assert_eq!(
                        got,
                        Some(u16::saturating_add(x, y) as u64),
                        "saturating_add u16 at ({x}, {y})"
                    );
                }
            }
        });
    }

    /// The signed division trap: `i8::MIN / -1` has no representable quotient, and
    /// the model must say `None` rather than hand back the wrapped value.
    #[test]
    fn signed_division_refuses_min_by_neg_one() {
        smt::with_fresh(|| {
            let a = smt::var(8);
            let b = smt::var(8);
            let op = Intrinsic::Checked(BinOp::Div);
            let outcome = eval(op, a, b, 8, true, 8).expect("i8 is modelled");
            let (ai, bi) = (smt::index(a), smt::index(b));
            let (got_some, _) = read(outcome, ai, bi, i8_bits(i8::MIN as i64), i8_bits(-1));
            assert_eq!(
                got_some,
                Some(false),
                "the model must not produce a quotient for i8::MIN / -1"
            );
            assert_eq!(i8::checked_div(i8::MIN, -1), None, "the oracle must agree");
        });
    }

    /// A name the model does not cover must be refused, not approximated. This is
    /// what keeps an unmodelled call from becoming a *silently weaker* proof.
    ///
    /// Refusal happens at two layers, and the distinction matters. A name whose
    /// *family and operator* are unknown does not classify at all. A name that
    /// classifies but whose shape cannot be modelled -- `saturating_div` panics on
    /// a zero divisor, so treating it as total would hide a panic -- is refused by
    /// `is_modelled`/`eval`. Both must refuse; neither may approximate.
    #[test]
    fn unmodelled_names_are_refused() {
        // Unknown operator: `pow` and `shl` are not in the operator table, so the
        // whole suffix fails to match.
        assert!(classify("saturating_pow").is_none());
        assert!(classify("wrapping_shl").is_none());
        assert!(classify("checked_shl").is_none());
        assert!(classify("unchecked_add").is_none());
        // The suffix is matched whole, so `wrapping_add_signed` is not read as
        // `wrapping_add`.
        assert!(classify("wrapping_add_signed").is_none());

        // A *known* operator that only some families can model. `saturating_div`
        // classifies as a name, and is then refused by the model: only the
        // `checked_` family may model division, because the others panic on zero.
        let sat_div = classify("core::num::<impl u8>::saturating_div")
            .expect("the name is recognised, so it classifies");
        assert_eq!(sat_div, Intrinsic::Saturating(BinOp::Div));
        assert!(
            eval(sat_div, smt::var(8), smt::var(8), 8, false, 8).is_none(),
            "saturating_div must not be modelled: it panics on a zero divisor"
        );
        assert!(!is_modelled(sat_div, 8, false));

        // And the names that *are* covered classify, under both spellings.
        assert!(classify("core::num::<impl u8>::checked_add").is_some());
        assert!(classify("saturating_sub").is_some());
    }

    /// Above the documented width limits the model declines rather than guessing.
    /// A declined model leaves the path unknown, which is the safe answer.
    #[test]
    fn past_the_width_limits_the_model_declines() {
        // Multiplication needs a `2w`-bit product; past `MUL_MAX_WIDTH` it declines.
        let mw = MUL_MAX_WIDTH + 1;
        assert!(eval(Intrinsic::Saturating(BinOp::Mul), smt::var(mw), smt::var(mw), mw, false, mw).is_none());
        // Division past `DIV_MAX_WIDTH` declines too.
        let dw = DIV_MAX_WIDTH + 1;
        assert!(eval(Intrinsic::Checked(BinOp::Div), smt::var(dw), smt::var(dw), dw, false, dw).is_none());
        // And the limits themselves are still modelled.
        assert!(eval(
            Intrinsic::Saturating(BinOp::Mul),
            smt::var(MUL_MAX_WIDTH),
            smt::var(MUL_MAX_WIDTH),
            MUL_MAX_WIDTH,
            false,
            MUL_MAX_WIDTH
        )
        .is_some());
        assert!(eval(
            Intrinsic::Checked(BinOp::Div),
            smt::var(DIV_MAX_WIDTH),
            smt::var(DIV_MAX_WIDTH),
            DIV_MAX_WIDTH,
            false,
            DIV_MAX_WIDTH
        )
        .is_some());
    }

    /// Walk every `w`-bit value and compare a unary model against Rust.
    ///
    /// The unary analogue of [`check`]: one operand, so one variable, and the
    /// result width is given separately because `count_ones` widens. `oracle`
    /// takes the operand's bit pattern and returns the expected result's bit
    /// pattern, calling the real `core` method so the expectation is not a
    /// second copy of the model.
    fn check_unary(
        op: Intrinsic,
        w: u8,
        result_w: u8,
        signed: bool,
        oracle: impl Fn(u64) -> u64,
        label: &str,
    ) {
        smt::with_fresh(|| {
            let a = smt::var(w);
            let outcome = eval(op, a, a, w, signed, result_w)
                .unwrap_or_else(|| panic!("{label} at {w} bits must be modelled"));
            let ai = smt::index(a);
            for xb in 0..(1u64 << w) {
                let want = oracle(xb);
                let Outcome::Value(v) = outcome else {
                    panic!("{label} must produce a plain value");
                };
                let got = smt::evaluate(v, |i| if i == ai { Some(xb) } else { None });
                assert_eq!(
                    got,
                    Some(want),
                    "{label} at bits {xb}: the model says {got:?}, Rust says {want}"
                );
            }
        });
    }

    /// `count_ones` counts the set bits, at every width, against Rust's own.
    ///
    /// The result type is wider than the operand (`u8` -> `u32`), which is the
    /// case the model has to widen; the same test at `result_w == w` covers the
    /// fixed-width reading. The exhaustive walk is what makes it a proof rather
    /// than a sample: every operand value is visited.
    #[test]
    fn count_ones_agrees_with_rust() {
        for w in [1u8, 4, 8] {
            check_unary(
                Intrinsic::Popcount,
                w,
                32,
                false,
                |b| u64::from((b as u32).count_ones()),
                "count_ones (widened to u32)",
            );
            check_unary(
                Intrinsic::Popcount,
                w,
                w,
                false,
                |b| u64::from((b as u32).count_ones()),
                "count_ones (at operand width)",
            );
        }
    }

    /// `wrapping_abs` agrees with Rust over every `i8`, `MIN` included.
    ///
    /// `MIN` is the interesting point: its magnitude is not representable, and
    /// Rust wraps it back to `MIN`. The model reaches that through `0 - x`
    /// wrapping, so this test is what pins that the shortcut is the same
    /// function as the method and not a near miss.
    #[test]
    fn wrapping_abs_agrees_with_rust() {
        check_unary(
            Intrinsic::Abs,
            8,
            8,
            true,
            |b| i8::from_ne_bytes([b as u8]).wrapping_abs() as u8 as u64,
            "wrapping_abs i8",
        );
    }

    /// `wrapping_abs` and `count_ones` classify, and their neighbours do not.
    ///
    /// The two are matched *before* the family split, so the names that would
    /// otherwise be read as `wrapping_` + an operator must still be refused:
    /// `wrapping_neg` is a real method this crate does not model, and reading it
    /// as the unknown operator `neg` would be a refusal anyway -- but reading
    /// `wrapping_abs` as the unknown operator `abs` would have made the *new*
    /// shape silently unmodelled, which is the failure this guards.
    #[test]
    fn the_unary_shapes_classify_and_their_neighbours_do_not() {
        assert_eq!(classify("core::num::<impl u8>::count_ones"), Some(Intrinsic::Popcount));
        assert_eq!(classify("count_ones"), Some(Intrinsic::Popcount));
        assert_eq!(classify("core::num::<impl i8>::wrapping_abs"), Some(Intrinsic::Abs));
        // Still refused: no operator named `neg`/`pow`/`abs` in the table, and
        // the family split only ever sees an operator name.
        assert!(classify("wrapping_neg").is_none());
        assert!(classify("checked_neg").is_none());
        assert!(classify("saturating_pow").is_none());
        // The near misses must not be read as the shapes that are modelled.
        assert!(classify("count_zeros").is_none());
        assert!(classify("leading_zeros").is_none());
        assert!(classify("trailing_zeros").is_none());
        assert!(classify("count_ones_signed").is_none());
        assert!(classify("wrapping_abs_signed").is_none());
    }

    /// The unary shapes are `is_unary`; the two-operand families are not.
    ///
    /// The executor branches on this to decide whether to read a second operand,
    /// so a family wrongly reported unary would read one argument and mis-shape
    /// every call, and a unary shape wrongly reported binary would refuse every
    /// call for missing its second argument.
    #[test]
    fn only_the_unary_shapes_are_unary() {
        assert!(Intrinsic::Popcount.is_unary());
        assert!(Intrinsic::Abs.is_unary());
        assert!(!Intrinsic::Wrapping(BinOp::Add).is_unary());
        assert!(!Intrinsic::Saturating(BinOp::Sub).is_unary());
        assert!(!Intrinsic::Checked(BinOp::Mul).is_unary());
    }
}
