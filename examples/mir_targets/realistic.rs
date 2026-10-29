//! Realistic Rust shapes, as a *coverage baseline* rather than a gate.
//!
//! `actuator.rs` next to this file is a regression corpus: every function in it
//! is expected to be decided, and the test suite asserts that. This file is the
//! opposite. It is a sample of the Rust a verifier meets in the wild, most of
//! which the frontend does *not* decide yet, and `examples/mir_coverage.rs`
//! reports which. Nothing here asserts a verdict, so adding a shape that fails
//! is the point rather than a broken test: it is how the gap is measured.
//!
//! Every shape below is decided: fields of by-value and by-reference structs,
//! tuple components, slice lengths and elements, fixed-size array lengths and
//! elements, `core::num` intrinsics and loops with invariants. The three
//! tripwires (`field_alias_tripwire`, `slice_alias_tripwire`,
//! `array_alias_tripwire`) *fail*, which is the evidence that two fields or two
//! elements are two distinct inputs rather than one aliased variable.
//!
//! The families this file was written to measure, and where each stands:
//!
//! * **Fields, elements and lengths.** *Closed.* A contract can name `c.lo` and
//!   `c.hi` on a by-value struct, `xs[0]` and `xs.len()` on a slice, and `a[0]`
//!   and `a.len()` on a fixed-size array. A slice's length is a symbolic input;
//!   an array's length is a type constant, so it is bound to `N` rather than to
//!   a fresh variable.
//! * **Loops have no invariant.** *Partly closed.* A loop without one is
//!   unwound to `DEFAULT_UNWIND` and reported incomplete; writing the invariant
//!   makes the frontend cut on it instead (`sum_to`, `count_up` and
//!   `count_evens` all carry one and verify). The invariant is not *inferred* —
//!   you supply the induction hypothesis, as in SPARK.
//! * **`core` is not modelled.** *Closed for the `num` intrinsics.*
//!   `checked_*`, `saturating_*` and `wrapping_*` are computed in the frontend
//!   from their operands rather than by reading `core`'s MIR.
//!
//! Keep the functions small. The point is to isolate one capability per
//! function, so a change that adds it moves exactly one row from `incomplete`
//! to `verified`.

#![allow(dead_code, clippy::all)]

// ---------------------------------------------------------------------------
// Must verify today: these are the shapes the frontend already decides.
// They are here so the scoreboard has a floor that must not regress.
// ---------------------------------------------------------------------------

/// requires: x > 0
/// ensures: ret <= x
pub fn halve_guarded(x: u8) -> u8 {
    x / 2
}

/// requires: a <= 3
/// ensures: ret == a + 1
pub fn increment_tiny(a: u8) -> u8 {
    a + 1
}

/// A literal in *arithmetic* is sized like one in a comparison.
///
/// The slice length puts a 64-bit name in scope, so `a + 5` would add an 8-bit
/// `a` to a 64-bit `5`. That is ill-formed, and an ill-formed term makes every
/// obligation in the run `Unknown` -- the same poisoning the comparison fix
/// addresses, reached through `+` instead of `<=`. The `*` and `&` forms are
/// sized the same way.
///
/// requires: a <= 250
/// ensures: ret == a + 5
pub fn add_literal_wide_scope(a: u8, xs: &[u8]) -> u8 {
    let _ = xs.len();
    a.wrapping_add(5)
}

/// requires: lo <= hi
/// ensures: ret <= hi
pub fn clamp_simple(lo: u8, hi: u8, v: u8) -> u8 {
    if v < lo {
        lo
    } else if v > hi {
        hi
    } else {
        v
    }
}

// ---------------------------------------------------------------------------
// Contracts that name a field, an element, or a length.
// ---------------------------------------------------------------------------

/// A struct passed by reference. The natural precondition is about two fields.
/// requires: c.lo <= c.hi
/// ensures: ret >= c.lo
pub fn pick_from(c: &Config, v: u8) -> u8 {
    if v < c.lo {
        c.lo
    } else if v > c.hi {
        c.hi
    } else {
        v
    }
}

/// A slice argument. The natural precondition is about its length.
/// requires: xs.len() > 0
/// ensures: ret == xs[0]
pub fn first_of(xs: &[u8]) -> u8 {
    xs[0]
}

/// A fixed-size array argument. Unlike a slice the length is a *type*
/// constant, so `a.len()` is not an input and the bounds check is against a
/// literal: `_3 = Lt(_2, const 4_usize)`. That literal is what makes this shape
/// a separate case from `first_of` -- the array's length never becomes a
/// symbolic variable, and the element width comes from `[u8; 4]` itself.
/// requires: a[0] <= a[1]
/// ensures: ret == a[1]
pub fn max_of_pair(a: [u8; 4]) -> u8 {
    if a[0] > a[1] {
        a[0]
    } else {
        a[1]
    }
}

/// The array-length tripwire: the same shape as `max_of_pair` but the contract
/// claims a bound the body does not meet. It must FAIL, and the counterexample
/// must assign `a[0]` and `a[1]` to *different* variables -- a pass would mean
/// the elements collapsed to one input and the array proof was vacuous.
/// requires: true
/// ensures: ret <= a[0]
pub fn array_alias_tripwire(a: [u8; 4]) -> u8 {
    if a[0] > a[1] {
        a[0]
    } else {
        a[1]
    }
}

/// The array length is a constant, so a contract can *rely* on it: `a.len()` is
/// `4` here regardless of the caller, which a slice's length never is.
/// requires: a.len() == 4
/// ensures: ret == a[2]
pub fn array_third(a: [u8; 4]) -> u8 {
    a[2]
}

/// A *symbolic* subscript of an array. `a[i]` is not a single element, but an
/// array has a finite domain, so it is the exact ite chain over `0..4` -- a
/// definition, not an approximation. The chain is only `a[i]` where `i < 4`, so
/// the precondition has to establish that; `i < 4` here is what makes the
/// subscript admissible, and without it the function is refused rather than
/// checked against a chain that quietly returned the last element.
/// requires: i < 4
/// ensures: ret == a[i]
pub fn array_symbolic_index(a: [u8; 4], i: usize) -> u8 {
    a[i]
}

/// The contract subscripts with an index *other* than the one the precondition
/// bounds. `requires: i < 4` says nothing about `j`, and `a[j]` is only modelled
/// where `j < 4`, so the contract is refused -- it is not silently rewritten to
/// the `a[i]` chain, which would prove `a[j] == a[i]` and be wrong for every
/// `i != j`. Both indices are live, so the refusal is about the contract's
/// subscript, not a dead argument.
/// requires: i < 4
/// ensures: ret == a[j]
pub fn array_wrong_index_refused(a: [u8; 4], i: usize, j: usize) -> u8 {
    let _ = a[j];
    a[i]
}

/// The contract subscripts with a name that is not an argument at all. There is
/// no variable to build a chain for `k`, so nothing is bound and the parser
/// refuses the name rather than inventing an index. This is the "no chain to
/// rewrite to" case, distinct from the unbounded one above.
/// requires: i < 4
/// ensures: ret == a[k]
pub fn array_local_index_refused(a: [u8; 4], i: usize) -> u8 {
    let k = i;
    a[k]
}

/// A symbolic subscript the precondition does *not* bound. `requires: true` says
/// nothing about `i`, so the ite chain would fall through for `i >= 4` and the
/// subscript is refused. This is the soundness gate for the whole feature.
/// requires: true
/// ensures: ret == a[i]
pub fn array_unbounded_index_refused(a: [u8; 4], i: usize) -> u8 {
    a[i]
}

/// A *slice* subscripted symbolically. A slice's length is a symbolic input, so
/// there is no finite domain to enumerate and no chain to build: `xs[i]` stays a
/// refusal. This is the boundary the feature is drawn at -- an array's length is
/// in its type, a slice's is not.
/// requires: i < 4
/// ensures: ret == xs[i]
pub fn slice_symbolic_index_refused(xs: &[u8], i: usize) -> u8 {
    xs[i]
}

/// An array built in the body, so the elements are concrete rather than inputs.
/// requires: true
/// ensures: ret == 20
pub fn array_literal_elem() -> u8 {
    let a = [10u8, 20, 30, 40];
    a[1]
}

/// A struct by value, to separate "field projection" from "behind a reference".
/// requires: c.lo <= c.hi
/// ensures: ret <= c.hi
pub fn clamp_by_value(c: Config, v: u8) -> u8 {
    if v < c.lo {
        c.lo
    } else if v > c.hi {
        c.hi
    } else {
        v
    }
}

/// A tuple return, whose components the postcondition would want to name.
/// requires: true
/// ensures: ret.0 <= a
pub fn split(a: u8, b: u8) -> (u8, u8) {
    if a < b {
        (a, b)
    } else {
        (b, a)
    }
}

pub struct Config {
    pub lo: u8,
    pub hi: u8,
}

// ---------------------------------------------------------------------------
// Gap 2: a loop cannot carry an invariant.
// ---------------------------------------------------------------------------

/// A counted loop whose result is bounded by its precondition.
/// requires: n <= 8
/// invariant: i <= n && s == i
/// ensures: ret <= 8
pub fn sum_to(n: u8) -> u8 {
    let mut s = 0u8;
    let mut i = 0u8;
    while i < n {
        s += 1;
        i += 1;
    }
    s
}

/// A loop that accumulates into a different variable, so a proof needs a
/// relation between two variables and not just a bound on one.
/// requires: n <= 4
/// invariant: i <= n
/// ensures: ret == n
pub fn count_up(n: u8) -> u8 {
    let mut i = 0u8;
    while i < n {
        i += 1;
    }
    i
}

/// A loop with a conditional body, which needs the invariant to survive a
/// branch rather than holding trivially.
/// requires: n <= 8
/// invariant: i <= n && c <= i
/// ensures: ret <= n
pub fn count_evens(n: u8) -> u8 {
    let mut c = 0u8;
    let mut i = 0u8;
    while i < n {
        if i % 2 == 0 {
            c += 1;
        }
        i += 1;
    }
    c
}

// ---------------------------------------------------------------------------
// `core::num` intrinsics: modelled directly rather than through their bodies.
//
// These were the "a call to `core` makes the path unknown" gap. `checked_*`,
// `saturating_*` and `wrapping_*` are now computed in the frontend from their
// operands, so the paths below are decided without `core`'s MIR being available.
// ---------------------------------------------------------------------------

/// `checked_add` is the idiomatic way to write this, and it is a `core` call.
/// requires: true
/// ensures: ret <= 1
pub fn is_nonzero_after(x: u8) -> u8 {
    match x.checked_add(1) {
        Some(_) => 1,
        None => 1,
    }
}

/// `saturating_sub` is likewise `core`, and it is the idiomatic clamp.
/// requires: a >= b
/// ensures: ret <= a
pub fn saturating_drop(a: u8, b: u8) -> u8 {
    a.saturating_sub(b)
}

/// `wrapping_mul` is `core`; a verifier has to know it is the wrapping product.
/// requires: a <= 15
/// ensures: ret <= 225
pub fn wrapped_product(a: u8) -> u8 {
    a.wrapping_mul(15)
}

/// A comparison through `core::cmp::Ord` rather than the builtin operator.
/// requires: true
/// ensures: ret <= a
pub fn min_via_ord(a: u8, b: u8) -> u8 {
    if a < b {
        a
    } else {
        b
    }
}

/// A field contract that must **fail**, as the tripwire for field independence.
///
/// If the frontend bound `c.lo` and `c.hi` to the same symbolic variable, this
/// would verify: with `lo == hi == x` the body returns `x` or `v == x`, so
/// `ret >= c.hi` would hold. Independent fields make it false — `v < c.lo`
/// returns `c.lo < c.hi` — so the counterexample is exactly the evidence that the
/// two fields are distinct inputs. `tests/mir.rs` requires the failure.
/// requires: c.lo <= c.hi
/// ensures: ret >= c.hi
pub fn field_alias_tripwire(c: Config, v: u8) -> u8 {
    if v < c.lo {
        c.lo
    } else if v > c.hi {
        c.hi
    } else {
        v
    }
}

/// A slice contract that must **fail**, as the tripwire for element independence.
///
/// If `xs[0]` and `xs[1]` were bound to the same symbolic variable, the body's
/// `xs[0]` would equal `xs[1]` and this would verify. Independent elements make
/// it false — take `xs[0] != xs[1]` — so the counterexample is exactly the
/// evidence that two indices are two inputs. `tests/mir.rs` requires the failure.
/// requires: xs.len() > 1
/// ensures: ret == xs[1]
pub fn slice_alias_tripwire(xs: &[u8]) -> u8 {
    xs[0]
}
