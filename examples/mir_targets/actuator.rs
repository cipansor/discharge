//! Functions under verification, with no `discharge` import at all.
//!
//! This file is ordinary Rust. It does not depend on the verifier, which is the
//! point: the code being checked and the tool doing the checking are separate
//! artifacts, and the tool reads this file's MIR rather than being linked into
//! it. It sits in a subdirectory so `cargo` does not build it as an example; the
//! demo and the test suite hand its path to the frontend instead.
//!
//! Contracts are doc comments (`requires:` / `ensures:`). See
//! `discharge::mir::spec` for why they are not attributes.

// This file is a *verification target*, not library code. The test suite compiles
// it so that counterexamples can be replayed against the real functions, which is
// why it allows lints that would otherwise push it toward shapes the verifier
// exists to check: rewriting `a - b` as `saturating_sub` would delete the very
// overflow the guard is there to prevent, and "unused function" is the normal
// state when the verifier rather than the program is the caller.
//
// The lint allows below are all the same trade. `eq_op` and `erasing_op` fire on
// the degenerate expressions the regression targets are *built from* -- `a == a`
// and `d & 0` are exactly the code a verifier must catch, and clippy is right
// that no human should write them. Rewriting them into lint-clean equivalents
// would delete the test.
#![allow(
    dead_code,
    clippy::implicit_saturating_sub,
    clippy::manual_checked_ops,
    clippy::eq_op,
    clippy::erasing_op,
    clippy::identity_op
)]

// ---------------------------------------------------------------------------
// Must verify: the guard and the arithmetic agree.
// ---------------------------------------------------------------------------

/// A clamp. The proof has to cover all three branches.
/// requires: lo <= hi
/// ensures: lo <= ret
/// ensures: ret <= hi
pub fn clamp(x: u32, lo: u32, hi: u32) -> u32 {
    if x < lo {
        lo
    } else if x > hi {
        hi
    } else {
        x
    }
}

/// A rate limiter: the command may not move more than 50 per tick, in either
/// direction.
/// requires: true
/// ensures: ret <= target
pub fn rate_limit(current: u32, target: u32) -> u32 {
    if target > current {
        let step = target - current;
        if step > 50 {
            current + 50
        } else {
            target
        }
    } else {
        target
    }
}

/// A saturating add written with a guard, so the `+` cannot overflow.
/// requires: true
/// ensures: ret >= a
pub fn sat_add(a: u16, b: u16) -> u16 {
    if a > u16::MAX - b {
        u16::MAX
    } else {
        a + b
    }
}

/// A saturating multiply, guarded the same way. This is the case the engine has
/// to work hardest for: the guard is a statement about a product.
/// requires: true
pub fn sat_mul(a: u16, b: u16) -> u16 {
    if b != 0 && a > u16::MAX / b {
        u16::MAX
    } else {
        a * b
    }
}

/// A guarded subtraction. `a - b` panics on underflow, so the guard is load
/// bearing.
/// requires: true
pub fn sat_sub(a: u16, b: u16) -> u16 {
    if b > a {
        0
    } else {
        a - b
    }
}

/// A *variable* shift with no guard of its own. rustc emits `assert(n < 16)`
/// before the shift, so `n == 16` is a real panic and must be reported; the
/// barrel shifter models the shift itself. This is the case that shows the
/// amount is now *modelled* rather than refused, while the panic is still found.
/// requires: true
pub fn shift_left(x: u16, n: u16) -> u16 {
    x << n
}

/// A shift by a constant. No guard is needed because the amount is in range, so
/// this proves on the cheap `Op::Shl` path.
/// requires: true
pub fn shift_const(x: u16) -> u16 {
    x << 3
}

/// A saturating variable shift, guarded the way real code guards one.
/// requires: true
pub fn sat_shift(x: u16, n: u16) -> u16 {
    if n >= 16 {
        0
    } else {
        x << n
    }
}

// ---------------------------------------------------------------------------
// Signed arithmetic. The unsigned cases above cannot tell a signed comparison
// from an unsigned one, so these exist to pin the difference.
// ---------------------------------------------------------------------------

/// A signed clamp. `lo <= hi` and the two comparisons must be *signed*: the
/// unsigned order calls `-1` the largest value, which would take the wrong
/// branch for every negative input.
/// requires: lo <= hi
/// ensures: lo <= ret
/// ensures: ret <= hi
pub fn clamp_signed(x: i32, lo: i32, hi: i32) -> i32 {
    if x < lo {
        lo
    } else if x > hi {
        hi
    } else {
        x
    }
}

/// A signed division whose guard excludes both traps: a zero divisor and the
/// `MIN / -1` overflow. rustc emits an assert for each.
/// requires: b != 0 && !(a == i16::MIN && b == -1)
/// ensures: true
pub fn checked_div_signed(a: i16, b: i16) -> i16 {
    a / b
}

/// A signed division with no guard at all, so the zero divisor and the
/// `MIN / -1` overflow are both reachable and both must be reported.
/// requires: true
pub fn unchecked_div_signed(a: i16, b: i16) -> i16 {
    a / b
}

/// A signed addition guarded on the *positive* side only. `a <= 127 && b <= 1`
/// reads like a safe guard and is not one: `127 + 1` overflows `i8`. The
/// unsigned overflow predicate would call this safe, because the wrapped sum
/// `128u8` is not below `127u8`; a signed predicate that compared the wrapped
/// sum signed would also call it safe. The correct test is the unsigned carry,
/// which fires here — this is the case that pins it.
/// requires: a <= 127 && b <= 1
/// ensures: true
pub fn signed_add_misguarded(a: i8, b: i8) -> i8 {
    a + b
}

/// A signed addition guarded on *both* ends of the range, which is what a signed
/// guard has to do. An upper bound alone is not enough: `a <= 60 && b <= 60`
/// admits `-128 + -128`, which overflows downward. The tempting unsigned-style
/// `a <= 100 && b <= 100` is wrong too — `100 + 100 = 200` overflows upward. A
/// magnitude bound of 60 admits no overflowing pair in either direction.
/// requires: a >= -60 && a <= 60 && b >= -60 && b <= 60
/// ensures: true
pub fn signed_add_guarded(a: i8, b: i8) -> i8 {
    a + b
}

/// A signed multiply guarded by magnitude, so it cannot overflow: the product of
/// two values of magnitude at most 10 is at most 100, well inside `i8`.
/// requires: a >= -10 && a <= 10 && b >= -10 && b <= 10
/// ensures: true
pub fn signed_mul_guarded(a: i8, b: i8) -> i8 {
    a * b
}

/// A signed multiply whose operands can be negative, where a zero-extending
/// widening would *understate* the product and miss the overflow. `-128 * -1`
/// overflows `i8`; the sign-extended widening sees it, the zero-extended one
/// would not.
/// requires: a <= 0 && b <= 0
/// ensures: true
pub fn signed_mul_negative(a: i8, b: i8) -> i8 {
    a * b
}

/// A signed negation guarded against `MIN`, which is the one input that has no
/// positive counterpart.
/// requires: a != i8::MIN
/// ensures: true
pub fn checked_neg(a: i8) -> i8 {
    -a
}

// ---------------------------------------------------------------------------
// Must fail: these are the bugs the frontend exists to find.
// ---------------------------------------------------------------------------
/// Plain `a + b` on `u16` with no guard. rustc emits `AddWithOverflow` and an
/// assert, so there is a reachable overflow and it must be reported.
/// requires: true
pub fn unchecked_add(a: u16, b: u16) -> u16 {
    a + b
}

/// The guard is off by one: `a <= MAX - b` admits the case where the sum is
/// exactly `MAX`, which is legal, and the overflow is still prevented. So this
/// function is panic-free — but its `ensures` is wrong, and that is the bug the
/// postcondition check has to catch.
/// requires: true
/// ensures: ret >= a
pub fn off_by_one_guard(a: u16, b: u16) -> u16 {
    if a <= u16::MAX - b {
        a + b
    } else {
        0
    }
}

/// Subtraction without a guard. Underflow is a real panic here.
/// requires: true
pub fn unchecked_sub(a: u16, b: u16) -> u16 {
    a - b
}

/// A divide with no zero check. rustc inserts the division-by-zero assert.
/// requires: true
pub fn unchecked_div(n: u32, d: u32) -> u32 {
    n / d
}

/// Multiplication without a guard, which overflows.
/// requires: true
pub fn unchecked_mul(a: u8, b: u8) -> u8 {
    a * b
}

// ---------------------------------------------------------------------------
// Regression targets for the four bugs the review found in the frontend.
// ---------------------------------------------------------------------------

/// A helper for the inlining targets. Small, total, and side-effect free.
pub fn callee_xor1(x: u8) -> u8 {
    x ^ 1
}

/// The caller saves its first argument in a local, calls another function, and
/// returns the saved value.
///
/// `requires: true`
/// `ensures: ret == a`
///
/// This must verify: the saved value is the caller's `a`, and the callee cannot
/// change it. It failed before the caller's environment was restored on return,
/// because the continuation read the callee's local `_1` — which held `b` — under
/// the caller's local number.
/// requires: true
/// ensures: ret == a
pub fn inline_saves_arg(a: u8, b: u8) -> u8 {
    let saved = a;
    let _ = callee_xor1(b);
    saved
}

/// The same shape with a postcondition that is actually false: the function
/// returns `a`, so `ret == b` cannot hold for every input.
///
/// The clobber bug made this verify, because the continuation read the callee's
/// `_1` (holding `b`) instead of the caller's saved `a`. It must now be refuted.
/// requires: true
/// ensures: ret == b
pub fn inline_clobber_would_pass(a: u8, b: u8) -> u8 {
    let saved = a;
    let _ = callee_xor1(b);
    saved
}

/// A `bool`-returning function whose postcondition is false.
///
/// `a == a` is always `true`, so `ret == false` is false for every input. Before
/// the fix, a `Val::Bool` return proved only that the returned bit was true and
/// never evaluated the declared postcondition, so this was reported verified.
/// requires: true
/// ensures: ret == false
pub fn bool_ret_false(a: u8) -> bool {
    a == a
}

/// The same function with the postcondition it actually satisfies, so the fix is
/// not "refuse every boolean return".
/// requires: true
/// ensures: ret == true
pub fn bool_ret_true(a: u8) -> bool {
    a == a
}

/// A contract wrapped in a redundant pair of parentheses.
///
/// `requires: ((a == 0))` means the same as `requires: (a == 0)`. The lookahead
/// that decides whether `(` opens a predicate used to test only depth one, so the
/// comparator at depth two was missed, the contract failed to parse, and the
/// function was skipped instead of verified.
/// requires: ((a == 0))
/// ensures: ret == a
pub fn nested_parens(a: u8) -> u8 {
    a
}

/// A precondition that no input satisfies. The contract proves nothing, and the
/// report must say so rather than returning `Verified` with a vacuous theorem.
/// requires: a < 3 && a > 10
/// ensures: ret == a
pub fn vacuous_precondition(a: u8) -> u8 {
    a
}

/// An add that overflows on *every* input the precondition admits.
///
/// The panic query is `a >= 128 && b >= 128 => can_overflow`, and `can_overflow`
/// is `true` under that guard for all inputs, so the query comes back `Valid`
/// rather than with a counterexample. That is the worst case, not a proof, and it
/// must be reported as a failure.
/// requires: a >= 128 && b >= 128
pub fn add_always_overflows(a: u8, b: u8) -> u8 {
    a + b
}

/// A divide by an expression that is zero on *every* input.
///
/// rustc lowers the zero check to `assert(!(divisor == 0))`, so the obligation is
/// "can the divisor be zero". Here `d & 0` is zero for every `d`, so the query is
/// `Valid` — the panic fires always. The obligation asks a reachability question,
/// so `Valid` is the worst answer, not a proof; reading `Valid` as "proved"
/// reports a function that always panics as verified.
/// requires: true
pub fn div_by_always_zero(a: u8, d: u8) -> u8 {
    let z = d & 0;
    a / z
}

/// A struct whose fields a contract names, in the regression corpus.
///
/// `realistic.rs` shows the capability; this file *requires* every function to be
/// decided, so putting it here makes a regression in field support a failing test
/// rather than a quietly-lower coverage number.
pub struct Bounds {
    /// The low bound.
    pub lo: u8,
    /// The high bound.
    pub hi: u8,
}

/// A clamp against a struct's fields, verified from the fields themselves.
///
/// The MIR dump prints `_1: &Bounds` and never the layout, so both the field
/// *index* and the field *width* come from the source. If the frontend lost
/// either, this would be skipped and the corpus test would fail.
/// requires: b.lo <= b.hi
/// ensures: ret >= b.lo && ret <= b.hi
pub fn clamp_bounds(b: &Bounds, v: u8) -> u8 {
    if v < b.lo {
        b.lo
    } else if v > b.hi {
        b.hi
    } else {
        v
    }
}
