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
//! * `overflowing_*` — a `(T, bool)`. The flag is the *same* predicate the other
//!   two families use, so the four cannot disagree about what "overflow" means.
//! * `wrapping_neg`, `checked_neg`, `saturating_neg`, `overflowing_neg` and the
//!   four `abs` spellings — the unary operators. They share the `0 - x` core,
//!   and `abs` is "negate if negative" on top of it, so there is one expression
//!   rather than four.
//! * `count_ones`, `leading_zeros`, `trailing_zeros` — bit counts, built at the
//!   operand's width and zero-extended to the *return* type's. `u8::count_ones`
//!   returns `u32`, so this is the one shape whose result is wider than its
//!   operand; the extension is the promotion Rust performs.
//!
//! # What is not, and why refusing is the right answer
//!
//! * `wrapping_div`, `wrapping_rem` and `saturating_div`/`saturating_rem` panic
//!   on a zero divisor. Modelling them as total would *hide a panic*, which is
//!   the one thing this frontend must never do. Only `checked_div` (which returns
//!   `None`) and `overflowing_div` (which returns a flag) can express the failure
//!   as a value, and only up to [`DIV_MAX_WIDTH`].
//! * The shifts are refused because the families disagree: `wrapping_shl` takes
//!   the amount modulo the width, while the engine's variable shift saturates to
//!   zero, and `checked_shl` returns `None` past the width. Three behaviours
//!   under one name is not something to guess at.
//! * `unchecked_*` is undefined behaviour on overflow. There is no value to
//!   model, and a proof about UB is not a proof, so it is refused.
//! * `pow` is the remaining gap. `pow(x, k)` is a `k`-fold product whose exponent
//!   is an *operand*, so its model needs the exponent's bits, and it is not
//!   written yet. `count_zeros`, `is_*`, `rotate_*`, `add_signed`, the float ops
//!   and the `next_multiple_of`/`div_*` helpers are likewise absent, and an
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
    /// The operation as `(T, bool)`: the wrapped result and whether it overflowed.
    /// Cannot fail.
    ///
    /// The flag is the *same* predicate the `checked_` family negates and the
    /// `saturating_` family branches on, so the three families cannot disagree
    /// about what "overflow" means.
    Overflowing(BinOp),
    /// A unary operator (`neg`, `abs`) in one of the four families.
    ///
    /// `neg` and `abs` are not two-operand operators, so they do not fit the
    /// `BinOp` variants above; they are unary *shapes* that each family happens to
    /// define. The family is carried because the four disagree about the failure
    /// case -- `wrapping_neg` returns the wrapped value, `checked_neg` returns
    /// `None`, `saturating_neg` clamps, `overflowing_neg` reports the flag.
    Unary(Family, UnOp),
    /// A bit count: `count_ones`, `leading_zeros` or `trailing_zeros`.
    ///
    /// Its result is wider than its operand (`u8::count_ones` returns `u32`), so
    /// unlike every other shape it is built at the operand's width and
    /// zero-extended to the destination's. It cannot fail.
    Bits(BitKind),
}

/// Which family of a `core::num` method name a call belongs to.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Family {
    /// `wrapping_*`: the result modulo `2^w`.
    Wrapping,
    /// `saturating_*`: the result clamped to the type's range.
    Saturating,
    /// `checked_*`: `Option<T>`.
    Checked,
    /// `overflowing_*`: `(T, bool)`.
    Overflowing,
}

/// A unary operator that each family defines.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum UnOp {
    /// Negation: `-x`.
    Neg,
    /// Absolute value: `|x|`.
    Abs,
}

/// A bit count.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BitKind {
    /// The number of set bits.
    Ones,
    /// The number of high zero bits, before the highest set bit.
    LeadingZeros,
    /// The number of low zero bits, before the lowest set bit.
    TrailingZeros,
}

impl Intrinsic {
    /// True for the shapes that take one operand and no operator.
    ///
    /// `eval` and the executor both branch on this: a unary call has no second
    /// argument to read, so the two-operand path must not be entered for it.
    pub fn is_unary(self) -> bool {
        matches!(self, Intrinsic::Unary(..) | Intrinsic::Bits(_))
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
    /// A `(T, bool)` tuple: the wrapped value and the overflow flag, for the
    /// `overflowing_*` family. Field 0 is the value and field 1 is the flag,
    /// which is the order rustc's own `(result, overflowed)` tuple uses.
    ///
    /// Unlike the `Option` tag, the flag is written as a `bool` and not as a
    /// word: nothing compares it to a variant discriminant, so it is read by a
    /// `bool` consumer (`assert(!flag)`, or a `ret.1` in a contract).
    Tuple { value: Var, overflowed: Pred },
}

/// The family a `core::num` method name belongs to, if any.
///
/// The name is matched after the last `::`, so both `core::num::<impl
/// u8>::checked_add` and a bare `checked_add` resolve. The whole suffix is
/// matched, not a prefix of it, so `wrapping_add_signed` and `saturating_pow`
/// are refused rather than read as `wrapping_add` and `saturating_add`.
///
/// The three bit counts are matched before the prefix split: they have no
/// `wrapping_`/`saturating_`/`checked_`/`overflowing_` prefix, and reading them
/// through the split would look for an operator named `ones`, `leading_zeros` or
/// `trailing_zeros` in the operator table. Matching them first keeps the split
/// honest -- it only ever sees a name it could actually have prefixed.
pub fn classify(name: &str) -> Option<Intrinsic> {
    let short = name.rsplit("::").next().unwrap_or(name);
    match short {
        "count_ones" => return Some(Intrinsic::Bits(BitKind::Ones)),
        "leading_zeros" => return Some(Intrinsic::Bits(BitKind::LeadingZeros)),
        "trailing_zeros" => return Some(Intrinsic::Bits(BitKind::TrailingZeros)),
        _ => {}
    }
    let (family, op) = if let Some(rest) = short.strip_prefix("wrapping_") {
        (Family::Wrapping, rest)
    } else if let Some(rest) = short.strip_prefix("saturating_") {
        (Family::Saturating, rest)
    } else if let Some(rest) = short.strip_prefix("overflowing_") {
        (Family::Overflowing, rest)
    } else {
        (Family::Checked, short.strip_prefix("checked_")?)
    };
    // `neg` and `abs` are unary, so they are their own shape rather than a
    // `BinOp`. Everything else in the families is a two-operand operator.
    match op {
        "neg" => return Some(Intrinsic::Unary(family, UnOp::Neg)),
        "abs" => return Some(Intrinsic::Unary(family, UnOp::Abs)),
        _ => {}
    }
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
        Family::Wrapping => Intrinsic::Wrapping(op),
        Family::Saturating => Intrinsic::Saturating(op),
        Family::Checked => Intrinsic::Checked(op),
        Family::Overflowing => Intrinsic::Overflowing(op),
    })
}

/// Whether the model has a definition for this operation at this width.
///
/// `w` is the *operand* width, not the return type's: `checked_add` on a `u8`
/// returns `Option<u8>` but overflows at 8 bits. `signed` decides what overflow
/// means, where the saturating bounds sit, and -- for the unary shapes -- whether
/// the method exists at all.
pub fn is_modelled(op: Intrinsic, w: u8, signed: bool) -> bool {
    if w == 0 || w > 64 {
        return false;
    }
    match op {
        // A bit count is a sum over the operand's bits, so it is exact at any
        // width the engine holds. Its *result* is wider than its operand, and
        // the model builds it at the operand's width and zero-extends.
        Intrinsic::Bits(_) => true,
        // The unary operators. Two membership facts decide whether a call can be
        // modelled at all, and both are about the *type*, not the width:
        //
        // * `abs` exists only on the signed types. `u8::wrapping_abs` is not a
        //   method, so a dump that calls it is either signed or not a real dump.
        // * `saturating_neg` exists only on the signed types too, while
        //   `wrapping_neg`, `checked_neg` and `overflowing_neg` exist on both.
        //   On an unsigned type negation is modular, and the failure case is
        //   `x != 0` -- which is exactly what the model computes once it reads
        //   the sign, so unsigned `neg` is modelled rather than refused.
        Intrinsic::Unary(family, un) => match un {
            UnOp::Abs => signed,
            UnOp::Neg => !(family == Family::Saturating && !signed),
        },
        // The two-operand families.
        Intrinsic::Wrapping(bin)
        | Intrinsic::Saturating(bin)
        | Intrinsic::Checked(bin)
        | Intrinsic::Overflowing(bin) => match bin {
            // Division is only modelled for the families that can express the
            // failure as a value: `checked_div` returns `None` and `overflowing_div`
            // returns a flag. The others panic on a zero divisor, and modelling
            // them as total would hide that panic.
            BinOp::Div | BinOp::Rem => {
                matches!(op, Intrinsic::Checked(_) | Intrinsic::Overflowing(_))
                    && w <= DIV_MAX_WIDTH
            }
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
/// differs from `w` only for the bit counts (`u8::count_ones` returns `u32`); for
/// every other shape the two are equal, and the caller passes `w` for both. The
/// result term is built at `result_w` so that it has the width of the local it is
/// written to -- a term narrower than its local would make the next read of that
/// local ill-formed.
pub fn eval(op: Intrinsic, x: Var, y: Var, w: u8, signed: bool, result_w: u8) -> Option<Outcome> {
    if !is_modelled(op, w, signed) || result_w == 0 || result_w > 64 {
        return None;
    }
    Some(match op {
        // The bit counts, each built at the operand's width and widened to the
        // result type. A count cannot exceed the operand width, so `w` bits hold
        // it; zero-extending to `result_w` is the promotion Rust performs (`u8`
        // -> `u32`). Building it wide here would add terms the extension throws
        // away, and for the fixed-width reading where `w == result_w` it is a
        // no-op.
        Intrinsic::Bits(kind) => Outcome::Value(smt::truncate(bit_count(kind, x), result_w)),
        Intrinsic::Unary(family, un) => {
            let fails = unary_failure(un, x, w, signed)?;
            let plain = unary_result(un, x, w);
            match family {
                // The wrapped value: `0 - x` for `neg`, `if x < 0 { 0 - x } else
                // { x }` for `abs`. For `abs` the `0 - x` wraps at `MIN`, where
                // the magnitude is unrepresentable, and that wrap *is* the
                // method's answer -- so no separate `MIN` case is needed, and
                // stating one would be a second definition that could drift.
                Family::Wrapping => Outcome::Value(smt::truncate(plain, result_w)),
                // The clamp. The bound is the sign of the *overflow*, which for
                // both unary operators is the sign `-x` cannot reach: a negative
                // `x` overflowing `neg` or `abs` clamps to `MAX`, and `MIN`
                // itself is the only `x` that overflows while being negative.
                Family::Saturating => {
                    let (_, hi) = bounds(w, signed)?;
                    Outcome::Value(smt::truncate(smt::ite(fails, hi, plain), result_w))
                }
                // The `Option`: the tag is `1` exactly where the operation is
                // defined, so the `switchInt` on it takes the `Some` arm on those
                // paths and the `None` arm on the rest. It is a term, not a
                // constant, and it is what lets the payload be recorded
                // unconditionally: rustc only reads the payload inside the `Some`
                // arm, where this tag is `1`.
                Family::Checked => Outcome::Option {
                    tag: smt::ite(fails, smt::word(0, w), smt::word(1, w)),
                    payload: smt::truncate(plain, result_w),
                },
                // The `(value, flag)` tuple. The flag is the *same* predicate the
                // other two families use, so they cannot disagree about what
                // "overflow" means.
                Family::Overflowing => {
                    Outcome::Tuple { value: smt::truncate(plain, result_w), overflowed: fails }
                }
            }
        }
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
            Outcome::Option {
                tag: smt::ite(fails, smt::word(0, w), smt::word(1, w)),
                payload: smt::truncate(plain, result_w),
            }
        }
        Intrinsic::Overflowing(bin) => {
            let plain = plain_result(bin, x, y, signed)?;
            let fails = failure(bin, x, y, w, signed)?;
            Outcome::Tuple { value: smt::truncate(plain, result_w), overflowed: fails }
        }
    })
}

/// The wrapped result of a unary operator, before any family reads it.
///
/// Both operators share the `0 - x` core, and that is not a coincidence worth
/// hiding: `abs` *is* "negate if negative", so `neg` is the one expression the
/// other is built from. `wrapping_neg` at `MIN` therefore returns `MIN`, which
/// is what Rust does, and `wrapping_abs` at `MIN` returns `MIN` for the same
/// reason -- both are `0 - MIN` wrapping.
fn unary_result(un: UnOp, x: Var, w: u8) -> Var {
    match un {
        UnOp::Neg => smt::sub(smt::word(0, w), x),
        UnOp::Abs => smt::ite(smt::negative(x), smt::sub(smt::word(0, w), x), x),
    }
}

/// When a unary operator has no representable result.
///
/// For `neg` that is when `-x` leaves the range. On a *signed* type only `MIN`
/// is unrepresentable, because `-MIN` is one past `MAX`; on an *unsigned* type
/// the result must be `0` to be representable, so every `x != 0` fails. That
/// difference is the whole content of the function, and it is why the sign has
/// to be read from the type rather than assumed.
///
/// For `abs` the magnitude is what must fit, and it does not only at `MIN` on a
/// signed type -- which is also exactly where `abs` negates, so the same
/// predicate serves both operators once the sign is known.
fn unary_failure(un: UnOp, x: Var, w: u8, signed: bool) -> Option<Pred> {
    match un {
        // `abs` needs a sign bit to have a magnitude at all, so an unsigned call
        // is refused by `is_modelled` and never reaches here. Answering anyway
        // would be a guess about a method that does not exist.
        UnOp::Abs if !signed => None,
        UnOp::Abs | UnOp::Neg if !signed => Some(smt::not(smt::eq_const(x, 0))),
        UnOp::Abs => Some(smt::eq_const(x, min_value(w)?)),
        UnOp::Neg => Some(smt::eq_const(x, min_value(w)?)),
    }
}

/// The number of bits of the requested kind, as a term of the *operand's* width.
///
/// All three are built from the same primitive -- "is bit `k` set" -- so they
/// cannot disagree about which bit is which.
fn bit_count(kind: BitKind, x: Var) -> Var {
    let w = smt::bits(x);
    let one = smt::word(1, w);
    let zero = smt::word(0, w);
    // `1` where bit `k` is set, `0` where it is not.
    let bit = |k: u8| smt::ite(smt::bit_set(x, u32::from(k)), one, zero);
    let mut acc = zero;
    match kind {
        // The set bits, summed.
        BitKind::Ones => {
            for k in 0..w {
                acc = smt::add(acc, bit(k));
            }
        }
        // The zero bits above the highest set bit. The `k`-th term is added only
        // while every bit above `k` is clear, which is `x < 2^k`. The sum runs
        // from `k == 0` and not from `k == 1`, and that is the whole subtlety:
        // `x < 2^0` is `x < 1`, which is `x == 0`, and a zero operand has *all*
        // `w` bits clear. Starting at `k == 1` omits that term and reports `w - 1`
        // for zero -- an off-by-one at exactly one input, which the exhaustive
        // walk against `core` is what caught.
        BitKind::LeadingZeros => {
            for k in 0..w {
                acc = smt::add(acc, smt::ite(smt::ult_const(x, 1u64 << k), one, zero));
            }
        }
        // The zero bits below the lowest set bit: the `k`-th term is added while
        // the low `k` bits are all clear. Written as `x & (2^k - 1) == 0`, which
        // is one `and` and one compare per bit.
        BitKind::TrailingZeros => {
            for k in 1..=w {
                let low = smt::band(x, smt::word((1u64 << k) - 1, w));
                acc = smt::add(acc, smt::ite(smt::eq_const(low, 0), one, zero));
            }
        }
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
            // A `(T, bool)`: the value is read like a plain one, and the flag is
            // reported through the same `Option<bool>` channel the `Option` tag
            // uses. The two are distinguishable by the caller because a `Tuple`
            // never has a `None` flag -- it is always `Some` -- while an `Option`
            // outcome's tag can be `0`. `check_tuple` reads it that way.
            Outcome::Tuple { value, overflowed } => {
                (smt::evaluate_pred(overflowed, env), smt::evaluate(value, env))
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
    /// result width is given separately because a bit count widens. `oracle`
    /// takes the operand's bit pattern and returns the expected result's bit
    /// pattern, calling the real `core` method so the expectation is not a second
    /// copy of the model.
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

    /// Walk every `w`-bit value and compare a unary `Option` model against Rust.
    ///
    /// `oracle` answers `Some(bits)` when the operation is defined and `None` when
    /// it is not, which is the shape a `checked_*` has. The tag is the model's
    /// "defined" bit and must agree with the oracle at every input -- a tag that
    /// says `Some` where Rust says `None` would let the `switchInt` take the wrong
    /// arm, and one that says `None` where Rust says `Some` would make a
    /// dischargeable obligation look unknown.
    fn check_unary_option(
        op: Intrinsic,
        w: u8,
        signed: bool,
        oracle: impl Fn(u64) -> Option<u64>,
        label: &str,
    ) {
        smt::with_fresh(|| {
            let a = smt::var(w);
            let outcome = eval(op, a, a, w, signed, w)
                .unwrap_or_else(|| panic!("{label} at {w} bits must be modelled"));
            let ai = smt::index(a);
            for xb in 0..(1u64 << w) {
                let want = oracle(xb);
                let Outcome::Option { tag, payload } = outcome else {
                    panic!("{label} must produce an `Option`");
                };
                let got_tag = smt::evaluate(tag, |i| if i == ai { Some(xb) } else { None });
                let got_val = smt::evaluate(payload, |i| if i == ai { Some(xb) } else { None });
                match want {
                    Some(v) => {
                        assert_eq!(
                            got_tag,
                            Some(1),
                            "{label} at bits {xb}: Rust says `Some`, model says {got_tag:?}"
                        );
                        assert_eq!(
                            got_val,
                            Some(v),
                            "{label} at bits {xb}: the model says {got_val:?}, Rust says {v}"
                        );
                    }
                    None => {
                        assert_eq!(
                            got_tag,
                            Some(0),
                            "{label} at bits {xb}: Rust says `None`, model says {got_tag:?}"
                        );
                    }
                }
            }
        });
    }

    /// Walk every `w`-bit value and compare a unary `(T, bool)` model against Rust.
    ///
    /// `oracle` answers with the wrapped value and the flag, which is the pair
    /// `overflowing_*` returns. The value is checked at *every* input, not only
    /// where the flag is clear, because the wrapped value is defined everywhere --
    /// that is what "wrapping" means.
    fn check_unary_tuple(
        op: Intrinsic,
        w: u8,
        signed: bool,
        oracle: impl Fn(u64) -> (u64, bool),
        label: &str,
    ) {
        smt::with_fresh(|| {
            let a = smt::var(w);
            let outcome = eval(op, a, a, w, signed, w)
                .unwrap_or_else(|| panic!("{label} at {w} bits must be modelled"));
            let ai = smt::index(a);
            for xb in 0..(1u64 << w) {
                let (want_val, want_flag) = oracle(xb);
                let Outcome::Tuple { value, overflowed } = outcome else {
                    panic!("{label} must produce a tuple");
                };
                let env = |i: u32| if i == ai { Some(xb) } else { None };
                assert_eq!(
                    smt::evaluate(value, env),
                    Some(want_val),
                    "{label} at bits {xb}: value mismatch"
                );
                assert_eq!(
                    smt::evaluate_pred(overflowed, env),
                    Some(want_flag),
                    "{label} at bits {xb}: overflow flag mismatch"
                );
            }
        });
    }

    /// The bit counts agree with Rust at every width, `count_ones` included.
    ///
    /// The result type is wider than the operand (`u8` -> `u32`), which is the
    /// case the model has to widen; the same test at `result_w == w` covers the
    /// fixed-width reading. The exhaustive walk is what makes it a proof rather
    /// than a sample: every operand value is visited.
    #[test]
    fn the_bit_counts_agree_with_rust() {
        // The oracle is `core`'s own method, read at the *operand's* width rather
        // than at `u32`. A count is a function of the bits of the type, and the
        // width is part of the answer: `0u8.leading_zeros()` is `8` and
        // `0u32.leading_zeros()` is `32`, while a one-bit zero has `1` of each.
        // Both counts are therefore taken at 32 bits and then adjusted, and
        // `trailing_zeros` gets a sentinel bit above the operand so that an
        // all-zero operand counts its own width instead of running into the
        // sentinel.
        fn oracle(kind: BitKind, w: u8, b: u64) -> u64 {
            let v = (b as u32) & ((1u32 << w) - 1);
            match kind {
                BitKind::Ones => u64::from(v.count_ones()),
                BitKind::LeadingZeros => u64::from(v.leading_zeros() - (32 - u32::from(w))),
                BitKind::TrailingZeros => u64::from((v | (1u32 << w)).trailing_zeros()),
            }
        }
        for w in [1u8, 4, 8] {
            for (kind, name) in [
                (BitKind::Ones, "count_ones"),
                (BitKind::LeadingZeros, "leading_zeros"),
                (BitKind::TrailingZeros, "trailing_zeros"),
            ] {
                let f = move |b: u64| oracle(kind, w, b);
                check_unary(
                    Intrinsic::Bits(kind),
                    w,
                    32,
                    false,
                    f,
                    &format!("{name} (widened to u32)"),
                );
                check_unary(
                    Intrinsic::Bits(kind),
                    w,
                    w,
                    false,
                    f,
                    &format!("{name} (at operand width)"),
                );
            }
        }
    }

    /// Every unary operator in every family agrees with Rust over a whole `i8`.
    ///
    /// `MIN` is the interesting point for all of them: its magnitude is not
    /// representable, so `neg` has no result, `abs` has no result, `saturating`
    /// clamps to `MAX`, `wrapping` returns `MIN`, `checked` returns `None` and
    /// `overflowing` reports the flag. One exhaustive walk per method is what
    /// proves the four families agree with `core` at that point *and* everywhere
    /// else, rather than only at the point that was reasoned about.
    #[test]
    fn the_signed_unary_families_agree_with_rust() {
        let x = |b: u64| i8::from_ne_bytes([b as u8]);
        let bits = |v: i8| v as u8 as u64;
        check_unary(
            Intrinsic::Unary(Family::Wrapping, UnOp::Neg),
            8,
            8,
            true,
            |b| bits(x(b).wrapping_neg()),
            "wrapping_neg i8",
        );
        check_unary(
            Intrinsic::Unary(Family::Saturating, UnOp::Neg),
            8,
            8,
            true,
            |b| bits(x(b).saturating_neg()),
            "saturating_neg i8",
        );
        check_unary_option(
            Intrinsic::Unary(Family::Checked, UnOp::Neg),
            8,
            true,
            |b| x(b).checked_neg().map(bits),
            "checked_neg i8",
        );
        check_unary_tuple(
            Intrinsic::Unary(Family::Overflowing, UnOp::Neg),
            8,
            true,
            |b| {
                let (v, o) = x(b).overflowing_neg();
                (bits(v), o)
            },
            "overflowing_neg i8",
        );
        check_unary(
            Intrinsic::Unary(Family::Wrapping, UnOp::Abs),
            8,
            8,
            true,
            |b| bits(x(b).wrapping_abs()),
            "wrapping_abs i8",
        );
        check_unary(
            Intrinsic::Unary(Family::Saturating, UnOp::Abs),
            8,
            8,
            true,
            |b| bits(x(b).saturating_abs()),
            "saturating_abs i8",
        );
        check_unary_option(
            Intrinsic::Unary(Family::Checked, UnOp::Abs),
            8,
            true,
            |b| x(b).checked_abs().map(bits),
            "checked_abs i8",
        );
        check_unary_tuple(
            Intrinsic::Unary(Family::Overflowing, UnOp::Abs),
            8,
            true,
            |b| {
                let (v, o) = x(b).overflowing_abs();
                (bits(v), o)
            },
            "overflowing_abs i8",
        );
    }

    /// Unsigned negation is modelled, and its failure case is `x != 0`.
    ///
    /// This is the case a "neg is signed" assumption would have refused
    /// outright. `u8::wrapping_neg` is the modular negation, `checked_neg` is
    /// `None` for every `x != 0`, and `overflowing_neg` reports the flag for the
    /// same set. `saturating_neg` does *not* exist unsigned, so `is_modelled`
    /// refuses it -- the one asymmetry between the families, and the reason the
    /// model reads the sign rather than assuming one.
    #[test]
    fn unsigned_negation_is_modelled_except_where_the_method_does_not_exist() {
        let bits = |v: u8| u64::from(v);
        check_unary(
            Intrinsic::Unary(Family::Wrapping, UnOp::Neg),
            8,
            8,
            false,
            |b| bits((b as u8).wrapping_neg()),
            "wrapping_neg u8",
        );
        check_unary_option(
            Intrinsic::Unary(Family::Checked, UnOp::Neg),
            8,
            false,
            |b| (b as u8).checked_neg().map(bits),
            "checked_neg u8",
        );
        check_unary_tuple(
            Intrinsic::Unary(Family::Overflowing, UnOp::Neg),
            8,
            false,
            |b| {
                let (v, o) = (b as u8).overflowing_neg();
                (bits(v), o)
            },
            "overflowing_neg u8",
        );
        // The members that do not exist on an unsigned type are refused.
        assert!(!is_modelled(Intrinsic::Unary(Family::Saturating, UnOp::Neg), 8, false));
        assert!(!is_modelled(Intrinsic::Unary(Family::Wrapping, UnOp::Abs), 8, false));
        assert!(!is_modelled(Intrinsic::Unary(Family::Checked, UnOp::Abs), 8, false));
        assert!(!is_modelled(Intrinsic::Unary(Family::Overflowing, UnOp::Abs), 8, false));
        // And they *are* modelled on a signed type.
        assert!(is_modelled(Intrinsic::Unary(Family::Saturating, UnOp::Neg), 8, true));
        assert!(is_modelled(Intrinsic::Unary(Family::Wrapping, UnOp::Abs), 8, true));
    }

    /// The unary shapes classify, and the names that only *look* like them do not.
    ///
    /// The family split must produce a `Unary` for `neg`/`abs` and a `BinOp` for
    /// everything else, so the near misses are the ones that would be read as the
    /// wrong shape: `neg_signed` is not an operator, `abs` without a prefix is not
    /// a method, and `pow` has no model yet.
    #[test]
    fn the_unary_names_classify_and_their_neighbours_do_not() {
        assert_eq!(
            classify("core::num::<impl i8>::wrapping_neg"),
            Some(Intrinsic::Unary(Family::Wrapping, UnOp::Neg))
        );
        assert_eq!(classify("wrapping_abs"), Some(Intrinsic::Unary(Family::Wrapping, UnOp::Abs)));
        assert_eq!(
            classify("core::num::<impl u8>::overflowing_neg"),
            Some(Intrinsic::Unary(Family::Overflowing, UnOp::Neg))
        );
        assert_eq!(
            classify("saturating_abs"),
            Some(Intrinsic::Unary(Family::Saturating, UnOp::Abs))
        );
        // `neg`/`abs` are *not* read as a `BinOp` operator.
        assert_eq!(classify("checked_neg"), Some(Intrinsic::Unary(Family::Checked, UnOp::Neg)));
        assert_ne!(classify("checked_neg"), Some(Intrinsic::Checked(BinOp::Add)));
        // Still refused.
        assert!(classify("neg").is_none());
        assert!(classify("abs").is_none());
        assert!(classify("wrapping_neg_signed").is_none());
        assert!(classify("checked_abs_signed").is_none());
        assert!(classify("saturating_pow").is_none());
        assert!(classify("wrapping_pow").is_none());
        assert!(classify("count_zeros").is_none());
        assert!(classify("count_ones_signed").is_none());
    }

    /// The bit-count names classify as counts and not as anything else.
    #[test]
    fn the_bit_count_names_classify() {
        assert_eq!(classify("core::num::<impl u8>::count_ones"), Some(Intrinsic::Bits(BitKind::Ones)));
        assert_eq!(classify("count_ones"), Some(Intrinsic::Bits(BitKind::Ones)));
        assert_eq!(classify("leading_zeros"), Some(Intrinsic::Bits(BitKind::LeadingZeros)));
        assert_eq!(classify("trailing_zeros"), Some(Intrinsic::Bits(BitKind::TrailingZeros)));
        // The near miss: `count_zeros` is a real method this crate does not model,
        // and it must not be read as `count_ones`.
        assert!(classify("count_zeros").is_none());
    }

    /// The unary shapes are `is_unary`; the two-operand families are not.
    ///
    /// The executor branches on this to decide whether to read a second operand,
    /// so a family wrongly reported unary would read one argument and mis-shape
    /// every call, and a unary shape wrongly reported binary would refuse every
    /// call for missing its second argument.
    #[test]
    fn only_the_unary_shapes_are_unary() {
        assert!(Intrinsic::Bits(BitKind::Ones).is_unary());
        assert!(Intrinsic::Unary(Family::Wrapping, UnOp::Neg).is_unary());
        assert!(Intrinsic::Unary(Family::Checked, UnOp::Abs).is_unary());
        assert!(!Intrinsic::Wrapping(BinOp::Add).is_unary());
        assert!(!Intrinsic::Saturating(BinOp::Sub).is_unary());
        assert!(!Intrinsic::Checked(BinOp::Mul).is_unary());
        assert!(!Intrinsic::Overflowing(BinOp::Add).is_unary());
    }
}
