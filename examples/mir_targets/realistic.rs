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
//! A second group at the end is the *soundness* tripwires: each is a false
//! contract that the frontend once proved because a write updated one of two
//! stores a place was held in, or because a generated binding could shadow a real
//! argument. They must fail (or be refused) for the same reason the alias
//! tripwires must: a `verified` verdict there is a proof of something untrue.
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

/// A struct with *signed* fields, for the signed-comparison shapes.
///
/// `Config`'s fields are `u8`, so a contract that needs `i8::MIN` cannot use it:
/// the bound would not fit the field's width. The signedness of a field is not in
/// the MIR dump (`_1.0: i8` appears only on the *copy* out of it), so the field
/// types have to come from here.
pub struct SignedConfig {
    pub lo: i8,
    pub hi: i8,
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

// ---------------------------------------------------------------------------
// Soundness tripwires: a write must reach the store the read consults.
// ---------------------------------------------------------------------------

/// An element write, then a *symbolic* read of the same array.
///
/// The seeded elements are what the ite chain is built from, so an element write
/// that landed anywhere other than the store the chain reads would leave the
/// chain selecting the *pre-write* element. The contract here is false -- with
/// `i == 0` the body returns the `0` it just wrote, not `a[i]` -- so it must
/// FAIL. A `verified` verdict would be a false contract proved, which is the one
/// outcome this crate exists to prevent.
/// requires: i < 4 && i == 0
/// ensures: ret == a[i]
pub fn array_write_then_symbolic_read(mut a: [u8; 4], i: usize) -> u8 {
    a[0] = 0;
    a[i]
}

/// The same shape through a `&mut [u8; 4]`, which is how a helper that mutates
/// its caller's array lowers.
///
/// The write goes through a reborrow, so it exercises the `(*_1)[0] = v` path
/// rather than the by-value one. The contract is false for the same reason as
/// `array_write_then_symbolic_read` -- with `i == 0` the body returns the `0` it
/// wrote -- so it must FAIL.
///
/// The `&mut [u8]` *slice* form of this shape is a separate gap, not this one:
/// rustc lowers it through a `&raw const (fake) (*_1)` reborrow whose
/// `PtrMetadata` the frontend does not model, so the function is incomplete
/// before any write is reached.
/// requires: i < 4
/// ensures: ret == a[i]
pub fn mut_ref_array_write_then_symbolic_read(a: &mut [u8; 4], i: usize) -> u8 {
    a[0] = 0;
    a[i]
}

/// A whole-struct reassignment, then a field read.
///
/// The contract's `c.lo` denotes the field of the *argument*, and the body
/// overwrites `c` with `d` before reading `c.lo`. The field bindings are keyed by
/// local, so an assignment that updated only the local would leave `c.lo` holding
/// the argument's value and this false contract (`ret` is `d.lo`, not `c.lo`)
/// would verify. It must be refused or refuted, never proved.
/// requires: true
/// ensures: ret == c.lo
#[allow(unused_assignments)]
pub fn struct_reassign_then_field_read(mut c: Config, d: Config) -> u8 {
    c = d;
    c.lo
}

/// A generated binding name that a real argument also uses.
///
/// The contract's `a[i]` is rewritten to a binding named `a__chain`, and the
/// function has an argument of exactly that name. If the generated binding were
/// allowed to shadow the argument, `ret == a__chain` would be checked against
/// the array's chain rather than against the argument the source names. The
/// contract is false for `i == 0 && a__chain == 0` with `a[0] != 0`, so it must
/// be refused or refuted, never proved.
/// requires: i < 4
/// ensures: ret == a__chain
#[allow(unused_variables, non_snake_case)]
pub fn generated_name_shadows_argument(a: [u8; 4], i: usize, a__chain: u8) -> u8 {
    a[i]
}

/// A helper that indexes its by-value array parameter, called from a contract.
///
/// The callee's `a[0]` must be the *same* symbolic input the caller passed, so
/// the caller's `ret == a[0]` is about the element the helper returned rather
/// than an unknown. Before the call handed the callee a copy of the indexed
/// store, the callee's `_1[_2]` had nothing to read and the caller was
/// incomplete.
/// requires: true
/// ensures: ret == a[0]
pub fn head(a: [u8; 4]) -> u8 {
    a[0]
}

/// The caller of [`head`], whose contract the helper's element read must satisfy.
/// requires: true
/// ensures: ret == a[0]
pub fn caller_of_head(a: [u8; 4]) -> u8 {
    head(a)
}

/// A helper that writes through a `&mut [u8; 4]` and returns the element.
///
/// The write is to the *caller's* storage, so on return the caller's `a[0]` is
/// the `0` the helper wrote, and `ret == 0` must verify.
/// requires: true
/// ensures: ret == 0
pub fn clear_head(a: &mut [u8; 4]) -> u8 {
    a[0] = 0;
    a[0]
}

/// The caller of [`clear_head`]: the helper's write to the shared store is what
/// makes `ret == 0` true here.
/// requires: true
/// ensures: ret == 0
pub fn caller_of_clear_head(a: &mut [u8; 4]) -> u8 {
    clear_head(a)
}

/// The by-value counterpart: a helper's write to its *own* copy must not reach
/// the caller.
///
/// `head_of` writes `a[0]` in its own frame and returns it; the caller's `a` is
/// the array it passed, untouched, so `ret == 0` is FALSE (the caller returns
/// its own `a[0]`). If the callee's copy were shared with the caller's store --
/// the tempting wrong model -- this would verify. It must fail.
/// requires: true
/// ensures: ret == 0
pub fn caller_of_written_copy(a: [u8; 4]) -> u8 {
    let _ = clear_copy(a);
    a[0]
}

/// A helper that clears its by-value copy and returns it.
/// requires: true
/// ensures: ret == 0
#[allow(unused_assignments)]
pub fn clear_copy(mut a: [u8; 4]) -> u8 {
    a[0] = 0;
    a[0]
}

/// A signed field compared against a signed constant, where the constant is the
/// *left* operand: `0 < c.lo`.
///
/// `0` here is `const 0_i8` in the dump, so the comparison is signed. Reading a
/// constant operand as unsigned made this an unsigned test, under which
/// `i8::MIN` (0x80) is the largest value and `ret == 1` was *proved* for
/// `c.lo == i8::MIN` -- a false proof, because `i8::MIN` is negative. It must
/// FAIL.
/// requires: c.lo == i8::MIN
/// ensures: ret == 1
pub fn signed_const_left_false(c: SignedConfig) -> u8 {
    if 0 < c.lo { 1 } else { 0 }
}

/// The true counterpart of [`signed_const_left_false`]: for `i8::MIN` the branch
/// is not taken, so `ret == 0` must verify.
/// requires: c.lo == i8::MIN
/// ensures: ret == 0
pub fn signed_const_left_true(c: SignedConfig) -> u8 {
    if 0 < c.lo { 1 } else { 0 }
}

/// A `(bool, u8)` tuple return with a postcondition on the bool component.
///
/// `ret.0` is a `bool` in the type but a one-bit word in the postcondition, so
/// the component has to be widened. Before that, `ret.0` had no binding and the
/// contract was refused as unreadable.
/// requires: a < 3
/// ensures: ret.0 == true
pub fn bool_component(a: u8) -> (bool, u8) {
    (a < 3, 0)
}

/// A `(u8, &u8)` return with a postcondition on the *first* component only.
///
/// Component 1 is a reference with no bit width, so binding every declared
/// component skipped the function. Only `ret.0`, which the contract names, needs
/// a binding.
/// requires: true
/// ensures: ret.0 == a
pub fn first_component_only(a: u8, r: &u8) -> (u8, &u8) {
    (a, r)
}

/// A tuple local whose component is read back: `let t = (a, b); t.0`.
///
/// `_3 = (a, b)` stores the components under an *index* projection, but rustc
/// prints the read as `_3.0` -- a *field* projection. The two spellings have to
/// meet in one store, or `t.0` reads `Unknown` and a contract about the return is
/// unreadable.
/// requires: true
/// ensures: ret == a
pub fn tuple_local_component(a: u8, b: u8) -> u8 {
    let t = (a, b);
    t.0
}

/// A helper returning a tuple.
/// requires: true
/// ensures: ret.0 == a || ret.0 == b
pub fn min2(a: u8, b: u8) -> (u8, bool) {
    if a < b { (a, true) } else { (b, false) }
}

/// A caller that reads a component of a tuple-returning call: `min2(a, b).0`.
///
/// The callee stores its result in its *own* return place (`_0.0`, `_0.1`), so
/// the components have to cross the call boundary with the aggregate; carrying
/// only the aggregate loses them and the contract is unreadable rather than
/// checked.
/// requires: true
/// ensures: ret == a || ret == b
pub fn min_call(a: u8, b: u8) -> u8 {
    min2(a, b).0
}

/// The soundness tripwire for the tuple-component read: the *other* component.
///
/// `t.0` is `a`, so claiming `ret == b` is false. If the field-projection
/// fallback into the element store picked the wrong component -- or read the
/// last-written one regardless of index -- this would verify. It must FAIL.
/// requires: true
/// ensures: ret == b
pub fn tuple_component_tripwire(a: u8, b: u8) -> u8 {
    let t = (a, b);
    t.0
}

/// The call-boundary counterpart: a false claim about the component that crossed.
///
/// `min2(a, b).0` is the smaller of the two, so claiming `ret == b` is false
/// whenever `a < b`. If the components crossed the boundary in the wrong order,
/// or as one shared value, this would verify. It must FAIL.
/// requires: true
/// ensures: ret == b
pub fn min_call_tripwire(a: u8, b: u8) -> u8 {
    min2(a, b).0
}

/// A signed widening cast sign-extends: `-1i8 as i16` is `-1`.
/// requires: a == -1
/// ensures: ret == -1
pub fn widen_signed_true(a: i8) -> i16 {
    a as i16
}

/// The soundness tripwire for the signed widening cast.
///
/// `truncate` zero-fills, so modelling every cast with it made `-1i8 as i16` the
/// bit pattern `255` -- and `ret == 255` was *proved* for `a == -1`, a reachable
/// false proof. The real value is `-1`. It must FAIL.
/// requires: a == -1
/// ensures: ret == 255
pub fn widen_signed_false(a: i8) -> i16 {
    a as i16
}

/// An unsigned widening cast zero-fills: `255u8 as u16` is `255`.
/// requires: a == 255
/// ensures: ret == 255
pub fn widen_unsigned_true(a: u8) -> u16 {
    a as u16
}

/// The counterpart tripwire for the unsigned widening: zero-filling is right
/// here, so `65535` is wrong and must FAIL. A single sign-extend-everything rule
/// would prove it.
/// requires: a == 255
/// ensures: ret == 65535
pub fn widen_unsigned_false(a: u8) -> u16 {
    a as u16
}

/// A comparison of a *signed* array element is a signed comparison.
///
/// This is the element-side counterpart of the `const 0_i8` case. The element's
/// signedness is a property of the array's element *type*, and it has to reach
/// the value the subscript produces. `i8::MIN` (0x80) is the most negative `i8`
/// and the largest `u8`, so the two readings of `xs[0] < 0` disagree on it:
/// signed says the branch is taken and returns `1`, unsigned says `0`. The
/// contract claims `1`, so it verifies only under the signed reading.
/// requires: xs.len() > 0 && xs[0] == i8::MIN
/// ensures: ret == 1
pub fn signed_slice_element_is_signed(xs: &[i8]) -> i8 {
    if xs[0] < 0 {
        1
    } else {
        0
    }
}

/// The tripwire for the signed element read.
///
/// The same body and the same precondition as
/// [`signed_slice_element_is_signed`], but the contract claims `0`. That is the
/// answer the *unsigned* reading gives -- an unsigned value is never below zero
/// -- so this false contract is *proved* by exactly the bug. It must FAIL, and
/// the counterexample is the element being negative.
/// requires: xs.len() > 0 && xs[0] == i8::MIN
/// ensures: ret == 0
pub fn signed_slice_element_tripwire(xs: &[i8]) -> i8 {
    if xs[0] < 0 {
        1
    } else {
        0
    }
}
