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
//!   `checked_*`, `saturating_*`, `wrapping_*` and `overflowing_*` are computed
//!   in the frontend from their operands rather than by reading `core`'s MIR.
//!   So are the unary operators — `neg` and `abs` in all four families — and the
//!   three bit counts `count_ones`, `leading_zeros` and `trailing_zeros`.
//!   Division is the one narrowing: only `checked_div`/`checked_rem` are
//!   modelled, because every other family — `overflowing_*` included — panics on
//!   a zero divisor and hiding that panic is not something a proof may do. A
//!   `(T, bool)` return read through `ret.1` reaches the component a modelled
//!   call wrote, which is the tuple-family coverage the `overflowing_*` block at
//!   the end pins.
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

/// The contract subscripts with a name that is not an argument — but which is a
/// *direct alias* of one. `let k = i;` of a `Copy` value lowers to no local at
/// all: the body's `a[k]` is `a[i]` (`_1[_2]`), and `k` survives only as a
/// scoped `debug k => _2;`. So the contract's `k` and the body's index are the
/// same value, and resolving the name makes the contract name what the body
/// reads. This is the "alias to an argument" case, distinct from the refusal
/// below where the name is not an alias at all.
/// requires: i < 4
/// ensures: ret == a[k]
pub fn array_local_index_through_alias(a: [u8; 4], i: usize) -> u8 {
    let k = i;
    a[k]
}

/// The tripwire for the alias: the same shape, with a postcondition that is
/// false. `a[k]` is an arbitrary element, so claiming it is at most `a[0]` must
/// FAIL — and the witness has to name an index where it is not, which only
/// happens if `k` resolved to the real index variable rather than to a constant
/// the contract happened to accept.
/// requires: i < 4
/// ensures: ret <= a[0]
pub fn array_local_index_tripwire(a: [u8; 4], i: usize) -> u8 {
    let k = i;
    a[k]
}

/// The alias rule's soundness gate: the local is a *copy* of the argument, and a
/// later write to the argument must not be aliased through.
///
/// `let k = i;` then `i = 2;` — after the write, `i` is 2 but `k` is still the
/// original argument. rustc does *not* print `debug k => _2;` here: it
/// materialises a real local for the copy, so `k` is not an alias of the
/// argument and the name is refused. That refusal is what keeps a contract's `k`
/// from silently following a reassigned `i`.
/// requires: i < 4
/// ensures: ret == a[k]
pub fn array_local_index_written_refused(a: [u8; 4], mut i: usize) -> u8 {
    let k = i;
    i = 2;
    a[k]
}

/// A subscript by a name that has been *shadowed* is refused.
///
/// `let k = i; let k = 0;` prints **two** bindings for `k`: `debug k => _2;` and,
/// nested deeper, `debug k => const 0_usize;`. Only the second is what the body's
/// `a[k]` reads. If the frontend resolved `k` from the first binding — which is
/// the only one that names a local — this contract would be checked against `i`
/// while the body used the constant: `requires: k == 0` would restrict `i` to 0
/// and `ensures: ret == a[i]` would prove, although the body returns `a[0]` and
/// the postcondition is false whenever `i == 1` and `a[0] != a[1]`. The name is
/// bound more than once, so it is refused rather than resolved.
/// requires: k == 0
/// ensures: ret == a[i]
pub fn array_shadowed_alias_refused(a: [u8; 4], i: usize) -> u8 {
    let k = i;
    let k = 0usize;
    a[k]
}

/// A contract that names the *same* index under two spellings verifies.
///
/// `a[i]` and `a[k]` with `let k = i` are one element, so a contract that uses
/// both must be readable — the second subscript has to rewrite to the same chain
/// as the first. Keeping only the first spelling left the second unrewritten and
/// the parser refused the whole contract, which skipped a function that should
/// have verified. This is a completeness gate, not a soundness one: the answer
/// was a refusal, never a wrong proof.
/// requires: i < 4
/// ensures: ret == a[k] && ret == a[i]
pub fn array_two_spellings_of_one_index(a: [u8; 4], i: usize) -> u8 {
    let k = i;
    a[k]
}

/// The tripwire for two spellings: both must name the *same* element.
///
/// `a[i]` and `a[k]` are the same subscript here, so claiming they differ must
/// FAIL. If the two spellings were rewritten to different chains — or one were
/// left as a fresh variable — this would verify, which is the wrong answer the
/// single-spelling code path was one step away from.
/// requires: i < 4
/// ensures: ret == a[i] && a[k] != a[i]
pub fn array_two_spellings_tripwire(a: [u8; 4], i: usize) -> u8 {
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

/// A *slice* subscripted symbolically, with both facts the model needs.
///
/// A slice's length is a symbolic input, so unlike an array there is no type
/// length to enumerate. The chain therefore enumerates `0..MAX_INDEX_CHAIN`, which
/// is an exact model of *every* index the slice holds -- and so of the index the
/// body reads -- but only where the length is within that bound. Both halves are
/// obligations on the precondition: `i < xs.len()` puts the named index in range,
/// and `xs.len() <= 64` keeps the whole slice inside the enumeration.
/// requires: i < xs.len() && xs.len() <= 64
/// ensures: ret == xs[i]
pub fn slice_symbolic_index(xs: &[u8], i: usize) -> u8 {
    xs[i]
}

/// The tripwire: the chain must genuinely depend on the index.
///
/// The body returns `xs[i]`, and the contract claims that is also `xs[0]` — false
/// for every `i != 0`. This must FAIL, with a witness pinning `i` to a non-zero
/// value. If the chain had collapsed to one element variable, or had been built
/// from element 0 regardless of `i`, this would verify.
///
/// The claim names `xs[i]` *and* `xs[0]` on purpose. Naming only the literal would
/// leave the body's symbolic read unmodelled — the chain is built when the
/// contract names a symbolic index — and the tripwire would come back a refusal
/// rather than a refutation, which a "not verified" assertion would accept for
/// the wrong reason.
/// requires: i < xs.len() && xs.len() <= 64
/// ensures: ret == xs[i] && ret == xs[0]
pub fn slice_symbolic_index_tripwire(xs: &[u8], i: usize) -> u8 {
    xs[i]
}

/// A slice whose *length* the precondition does not bound.
///
/// `i < xs.len()` puts the index in range, but says nothing about how long the
/// slice is, and the chain can only enumerate `0..64`. An index past 64 would fall
/// through it, so the subscript is refused rather than modelled. This is the half
/// an index-only bound would miss.
/// requires: i < xs.len()
/// ensures: ret == xs[i]
pub fn slice_unbounded_length_refused(xs: &[u8], i: usize) -> u8 {
    xs[i]
}

/// A slice whose *index* the precondition does not bound, with the length bounded.
///
/// The mirror of the entry above: `xs.len() <= 64` keeps the chain's range honest,
/// but nothing says `i` is in it, so `xs[i]` is refused. Two separate obligations,
/// each with its own refusal.
/// requires: xs.len() <= 64
/// ensures: ret == xs[i]
pub fn slice_unbounded_index_refused(xs: &[u8], i: usize) -> u8 {
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

impl Config {
    pub fn set_lo(&mut self, v: u8) {
        self.lo = v;
    }

    pub fn bump_lo(&mut self) {
        self.lo = self.lo + 1;
    }

    pub fn set_hi(&mut self, v: u8) {
        self.hi = v;
    }
}

/// A fieldless enum, for the `match` shapes at the end of the file.
///
/// Its variants are declared in one line, which is the shape a one-line reader
/// has to handle: the discriminants are `0`, `1` and `2` in declaration order,
/// and a `match` on it lowers to `switchInt(discriminant(m))` over those.
pub enum Mode { Off, Idle, Run }

/// An enum with a payload, for the downcast shapes.
///
/// `Msg::Data(u8)` puts a `u8` in variant `1`, so the `match` arm reads it back
/// as `((_1 as Data).0)`. The other two variants are unit variants with no
/// payload to read, which is what the payload tripwire relies on.
pub enum Msg { Ping, Data(u8), Stop }

/// An enum with an *explicit* discriminant, for the numbering shapes.
///
/// `B = 3` makes rustc assign `C` the discriminant `4`, not the position `1` that
/// a reader numbering by declaration order would give it. A contract naming
/// `Gap::C` must mean tag `4`, and a `match` arm on `Gap::C` compares against `4`;
/// numbering by position would put the contract and the arm in disagreement.
pub enum Gap { A, B = 3, C }

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
/// requires: i < 4
/// ensures: ret == a[i]
pub fn mut_ref_array_write_then_symbolic_read(a: &mut [u8; 4], i: usize) -> u8 {
    a[0] = 0;
    a[i]
}

/// The `&mut [u8]` *slice* form of the same shape.
///
/// This used to be a separate gap: rustc lowers the bounds check through a
/// `&raw const (fake) (*_1)` reborrow whose `PtrMetadata` the frontend did not
/// model, so the function was `incomplete` before any write was reached. The
/// parser now reads `&raw const (fake) (place)` as the place it names, so the
/// slice shape is modelled like the array one.
///
/// The contract is false for the same reason -- with `i == 0` the body returns
/// the `0` it wrote, not `s[i]` -- so it must FAIL. A `verified` verdict would be
/// a false contract proved.
/// requires: i < s.len() && s.len() <= 64 && i == 0
/// ensures: ret == s[i]
pub fn mut_ref_slice_write_then_symbolic_read(s: &mut [u8], i: usize) -> u8 {
    s[0] = 0;
    s[i]
}

/// The true half of the slice shape: a write then a read of the *same* index
/// returns what was written, and the `s.len() > 0` precondition puts index `0`
/// in range so the bounds check is discharged rather than a panic.
///
/// This is the entry that shows the write reaches the store the read consults:
/// if the write had landed anywhere else, the read would find the seeded element
/// and the contract would be refuted, not proved.
/// requires: s.len() > 0
/// ensures: ret == v
pub fn mut_ref_slice_write_then_read(s: &mut [u8], v: u8) -> u8 {
    s[0] = v;
    s[0]
}

/// The tripwire for the true half above: the same body claiming the *pre-write*
/// value is false, so a model that dropped the write -- leaving the seeded
/// element readable -- would prove it.
/// requires: s.len() > 0
/// ensures: ret == s[0]
pub fn mut_ref_slice_write_then_read_tripwire(s: &mut [u8], v: u8) -> u8 {
    s[0] = v;
    s[0]
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

/// A field *write* through a `&mut`: `c.lo = 5`.
///
/// The write is the mirror of the read, and it is the shape that was silently
/// dropped. MIR spells it `((*_1).0: u8) = const 5_u8`, a `Deref` then a `Field`,
/// and a store that modelled `Deref, Index` but not `Deref, Field` fell through to
/// the drop arm. The consequence was two-sided: the write did not take effect, so a
/// true contract was refuted (the read saw the caller's old value) *and* a false
/// contract could be proved (the postcondition was checked against the value the
/// write was supposed to replace). This entry pins the true direction: the write
/// lands and the read after it is `5`, so `ret == 5` verifies.
/// requires: true
/// ensures: ret == 5
pub fn field_write_through_ref_mut_takes_effect(c: &mut Config) -> u8 {
    c.lo = 5;
    c.lo
}

/// The false direction of [`field_write_through_ref_mut_takes_effect`].
///
/// The body writes `5` and returns it, so `ret == 0` is false for every input. With
/// the write dropped, the read saw the caller's unconstrained `c.lo` and the
/// postcondition was checked against a variable the write never touched, which made
/// this *provable* -- a false proof in already-shipped code. It must be refuted, and
/// the refutation must be "false on every input" rather than a one-value witness:
/// that is the term-level evidence the write fixes `ret` to `5`.
/// requires: true
/// ensures: ret == 0
pub fn field_write_through_ref_mut_is_not_dropped(c: &mut Config) -> u8 {
    c.lo = 5;
    c.lo
}

/// A helper writes a field through a `&mut` argument.
pub fn set_lo_through_ref(c: &mut Config) {
    c.lo = 5;
}

/// A scalar helper writes through a `&mut` argument.
pub fn set_five(v: &mut u8) {
    *v = 5;
}

/// A scalar helper that writes its own *by-value* argument and returns it.
pub fn set_five_by_value(mut x: u8) -> u8 {
    x = 5;
    x
}

/// A helper's field write through a `&mut` reaches the caller.
///
/// The write happens one frame down: `set_lo_through_ref(c)` runs `c.lo = 5` in
/// the callee, and the caller's `c.lo` must be 5 when it returns. This is the
/// boundary the write-back used to miss -- only an *indexed* reference argument's
/// store crossed back, so a field write died with the callee's frame and the
/// caller read its own seed.
/// requires: true
/// ensures: ret == 5
pub fn helper_field_write_reaches_the_caller(c: &mut Config) -> u8 {
    set_lo_through_ref(c);
    c.lo
}

/// The false direction of [`helper_field_write_reaches_the_caller`].
///
/// The helper sets `c.lo = 5` and the caller returns it, so `ret == 0` is false.
/// With the field write lost across the boundary, the caller's `c.lo` kept the
/// seed the precondition pinned to 0, so this was *proved* against a body that
/// returns 5.
/// requires: c.lo == 0
/// ensures: ret == 0
pub fn a_stale_caller_field_cannot_prove_this(c: &mut Config) -> u8 {
    set_lo_through_ref(c);
    c.lo
}

/// A helper's write to the *whole* referent (`*v = 5`) reaches the caller.
///
/// `&mut x` is passed as a temp (`_5 = &mut _2; set_five(_5)`), so the caller's
/// storage is `_2` while the callee's argument local is `_5`. The write-back has
/// to follow the recorded address to `_2`, and the callee's own `(*_1) = 5` has to
/// be modelled at all: a deref of an argument with no recorded referent was
/// dropped, so the write vanished twice over.
/// requires: true
/// ensures: ret == 5
pub fn helper_scalar_write_reaches_the_caller(mut x: u8) -> u8 {
    set_five(&mut x);
    x
}

/// The false direction of [`helper_scalar_write_reaches_the_caller`].
///
/// The helper writes `5` and the caller returns it, so `ret == 0` is false. With
/// both the callee's write and the write-back lost, the caller read its seed and
/// this was *proved*.
/// requires: x == 0
/// ensures: ret == 0
pub fn a_stale_caller_scalar_cannot_prove_this(mut x: u8) -> u8 {
    set_five(&mut x);
    x
}

/// A helper writes a *nested* field through a `&mut` argument.
pub fn set_nested_through_ref(o: &mut OuterBox) {
    o.i.v = 9;
}

/// A helper reads and writes the same field through a `&mut` argument.
pub fn add_lo_through_ref(c: &mut Config, d: u8) {
    c.lo = c.lo + d;
}

/// A helper that writes through a `&mut` only on one branch.
pub fn set_five_if(v: &mut u8, c: bool) {
    if c {
        *v = 5;
    }
}

/// A helper's *nested* field write through a `&mut` reaches the caller.
/// requires: true
/// ensures: ret == 9
pub fn helper_nested_write_reaches_the_caller(o: &mut OuterBox) -> u8 {
    set_nested_through_ref(o);
    o.i.v
}

/// The false direction of [`helper_nested_write_reaches_the_caller`].
/// requires: true
/// ensures: ret == 0
pub fn a_stale_caller_nested_cannot_prove_this(o: &mut OuterBox) -> u8 {
    set_nested_through_ref(o);
    o.i.v
}

/// A helper writes through a `&mut` to a *field* of the caller's struct.
///
/// The reference names a sub-place (`&mut c.lo`), so the callee's write belongs at
/// `c.0` and not on `c`. Landing it on `c` would put a bit-vector where a struct
/// lives and leave `c.lo` at its seed -- which is why the false twin below was
/// *proved* before the write-back keyed the target's projection.
/// requires: c.lo == 0
/// ensures: ret == 5
pub fn helper_write_reaches_a_field_target(mut c: Config) -> u8 {
    set_five(&mut c.lo);
    c.lo
}

/// The false direction of [`helper_write_reaches_a_field_target`].
/// requires: c.lo == 0
/// ensures: ret == 0
pub fn a_stale_field_target_cannot_prove_this(mut c: Config) -> u8 {
    set_five(&mut c.lo);
    c.lo
}

/// A helper write through a `&mut` to a *nested* field target.
///
/// The reference names a two-step chain (`&mut o.i.v`), so the write-back has to
/// key the whole chain, not just the first field.
/// requires: true
/// ensures: ret == 5
pub fn helper_write_reaches_a_nested_target(mut o: OuterBox) -> u8 {
    set_five(&mut o.i.v);
    o.i.v
}

/// The false direction of [`helper_write_reaches_a_nested_target`].
/// requires: o.i.v == 0
/// ensures: ret == 0
pub fn a_stale_nested_target_cannot_prove_this(mut o: OuterBox) -> u8 {
    set_five(&mut o.i.v);
    o.i.v
}

/// A *conditional* helper write: the caller reads 5 when the flag holds and its
/// seed otherwise, so the caller's value has to follow the callee's branch.
/// requires: c == true
/// ensures: ret == 5
pub fn conditional_helper_write_reaches_the_caller(mut x: u8, c: bool) -> u8 {
    set_five_if(&mut x, c);
    x
}

/// The false direction of [`conditional_helper_write_reaches_the_caller`].
/// requires: x == 0 && c == true
/// ensures: ret == 0
pub fn a_conditional_helper_write_cannot_prove_this(mut x: u8, c: bool) -> u8 {
    set_five_if(&mut x, c);
    x
}

/// A helper writes through a `&mut` to an *array element* target.
///
/// The reference names `a[0]`, so the callee is handed a scalar and its store for
/// that local is the caller's array carried in for the read. Copying the callee's
/// store back unconditionally would carry the poison its whole-place write left on
/// that store, so the caller's *untouched* `a[1]` would read unknown. Gating the
/// element copy-back on a whole-local target is what keeps the sibling readable.
/// requires: true
/// ensures: ret == 5
pub fn helper_write_reaches_an_element_target(mut a: [u8; 3]) -> u8 {
    set_five(&mut a[0]);
    a[0]
}

/// The false direction of [`helper_write_reaches_an_element_target`].
/// requires: a[0] == 0
/// ensures: ret == 0
pub fn a_stale_element_target_cannot_prove_this(mut a: [u8; 3]) -> u8 {
    set_five(&mut a[0]);
    a[0]
}

/// A write to one element leaves its *sibling* alone.
/// requires: a[1] == 7
/// ensures: ret == 7
pub fn an_element_write_leaves_its_sibling(mut a: [u8; 3]) -> u8 {
    set_five(&mut a[0]);
    a[1]
}

/// The false direction of [`an_element_write_leaves_its_sibling`].
/// requires: a[1] == 7
/// ensures: ret == 0
pub fn a_stale_element_sibling_cannot_prove_this(mut a: [u8; 3]) -> u8 {
    set_five(&mut a[0]);
    a[1]
}

/// A callee's write to a *by-value* argument is its own copy and must not reach
/// the caller.
/// requires: x == 3
/// ensures: ret == 3
pub fn a_by_value_callee_write_stays_in_the_callee(x: u8) -> u8 {
    let _ = set_five_by_value(x);
    x
}

/// The false direction of [`a_by_value_callee_write_stays_in_the_callee`]: if the
/// callee's write leaked back, `ret == 5` would prove.
/// requires: x == 3
/// ensures: ret == 5
pub fn a_by_value_callee_write_cannot_prove_this(x: u8) -> u8 {
    let _ = set_five_by_value(x);
    x
}

/// A method that writes a field through `&mut self`.
///
/// An inherent method is *defined* as `<impl at file:line:col>::set_lo` and *called*
/// as `Config::set_lo`, so a name match has to cut both sides to their last `::`
/// component. Without that, every method call was "unmodelled function" and a
/// method's write through `&mut self` could not be seen by its caller.
pub fn method_set_lo(c: &mut Config, v: u8) {
    c.lo = v;
}

/// A method's write through `&mut self` reaches the caller.
/// requires: true
/// ensures: ret == 5
pub fn a_method_write_reaches_the_caller(mut c: Config) -> u8 {
    c.set_lo(5);
    c.lo
}

/// The false direction of [`a_method_write_reaches_the_caller`].
/// requires: c.lo == 0
/// ensures: ret == 0
pub fn a_method_write_cannot_prove_this(mut c: Config) -> u8 {
    c.set_lo(5);
    c.lo
}

/// A read-modify-write *method*.
/// requires: c.lo == 3
/// ensures: ret == 4
pub fn a_method_read_modify_write(mut c: Config) -> u8 {
    c.bump_lo();
    c.lo
}

/// A method writing one field leaves its *sibling* alone.
/// requires: c.lo == 7
/// ensures: ret == 7
pub fn a_method_leaves_its_sibling(mut c: Config) -> u8 {
    c.set_hi(9);
    c.lo
}

/// The false direction of [`a_method_leaves_its_sibling`].
/// requires: c.lo == 7
/// ensures: ret == 9
pub fn a_stale_sibling_cannot_prove_this(mut c: Config) -> u8 {
    c.set_hi(9);
    c.lo
}

/// A read-modify-write helper through a `&mut` is modelled, not left incomplete.
///
/// The callee reads `c.lo` before writing it, so the caller's field seed has to
/// cross *into* the callee as well as back out. Carrying only the write-back would
/// leave the callee's read unmodelled and this contract incomplete.
/// requires: c.lo == 3
/// ensures: ret == 8
pub fn read_modify_write_through_helper(c: &mut Config) -> u8 {
    add_lo_through_ref(c, 5);
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

/// A *contract literal* widened to meet a signed operand zero-fills, because the
/// literal's own signedness is what decides the fill, not the operand's.
///
/// Rust's `(255u8 as i16)` is `255`, not `65535`, so `(x as i16) == 255` holds for
/// every `u8` `x`. The reader widened the literal `255` to the operand's signed
/// `i16` by *sign-extending* it -- filling from the operand's sign instead of the
/// constant's -- giving `65535`, and refuted a postcondition Rust accepts: a false
/// *refutation*, the mirror of a false proof. It must verify.
/// requires: x == 255
/// ensures: (x as i16) == 255
pub fn contract_literal_widened_to_signed_zero_fills(x: u8) -> u8 {
    x
}

/// The control that the fix did not simply stop widening or verify everything:
/// `254` is neither the zero-filled nor the sign-extended reading of `255`, so
/// this is false in Rust and must FAIL.
/// requires: x == 255
/// ensures: (x as i16) == 254
pub fn contract_literal_widened_to_signed_tripwire(x: u8) -> u8 {
    x
}

/// The soundness tripwire for an *untyped* (opaque) constant widened to an
/// unsigned operand.
///
/// A complement's value is taken at the *operand's* width, but the reader holds it
/// at the *scope's*. `!0` against a `u16` is `65535`, so `(x as u16 + !0) == 255`
/// is false in Rust; the reader held `255` and zero-extended it, and *verified* the
/// equality -- a false proof. The shape is refused, so this must not verify.
/// requires: x == 0
/// ensures: (x as u16 + !0) == 255
pub fn contract_opaque_widened_to_unsigned_is_refused(x: u8) -> u8 {
    x
}

/// The signed counterpart, which fails the same way when the literal's top bit is
/// clear: `!128` against an `i16` is `-129`, not `127`. Also refused.
/// requires: x == 0
/// ensures: (x as i16 + !128) == 127
pub fn contract_opaque_widened_to_signed_is_refused(x: u8) -> u8 {
    x
}

/// The control: a *fold* (`200 + 100` = `300`) is a value, not a width-dependent
/// bit pattern, so it widens into a `u16` exactly and must verify.
/// requires: x <= 100
/// ensures: (x as u16) <= 200 + 100
pub fn contract_fold_widens_to_unsigned_reads(x: u8) -> u8 {
    x
}

/// A *suffixed* literal keeps its own width, so a cast of it is not re-read from
/// the names in scope.
///
/// `128i16` is a sixteen-bit `128`, and `128i16 as i32` is `128` in Rust. The
/// reader sized the literal from the scope instead -- with only `u8` names that is
/// eight bits, so `128i16` was `0x80`, read as `-128`, and `128i16 as i32` became
/// `-128`. The false postcondition below was *verified* under that reading and is
/// false in Rust, so it must not verify.
/// requires: x == 0
/// ensures: 128i16 as i32 == -128
pub fn contract_suffixed_literal_keeps_its_width(x: u8) -> u8 {
    x
}

/// The true counterpart: `128i16 as i32` is `128`, so this must verify.
/// requires: x == 0
/// ensures: 128i16 as i32 == 128
pub fn contract_suffixed_literal_is_its_own_value(x: u8) -> u8 {
    x
}

/// The false proof that a *fold* of a complement was read at the scope's width.
///
/// `!0` is `-1` in Rust, so `!0 + 2` is `1`, and `(x as i16 + 2) == !0 + 2` is
/// false. The reader held the complement at the scope's width (`255`), added `2`
/// to get `257`, and a later resize truncated it into `i16`'s `1`, *verifying* the
/// false equality. The fold must not verify now.
/// requires: x == 255
/// ensures: (x as i16 + 2) == !0 + 2
pub fn contract_complement_fold_widening_is_refused(x: u8) -> u8 {
    x
}

/// An untyped fold that *overflows* the operand width is refused, not truncated
/// into a verdict.
///
/// `!0 + 1` is `0` against an `i8` but is a rustc `arithmetic operation will
/// overflow` error against a `u8` (`!0` is `255`). The reader held the fold at the
/// scope's width (`256`) and truncated it to the `u8` partner's width, so
/// `(!0 + 1) < 1u8` *verified* (`0 < 1`) for a program rustc rejects. The fold's
/// value depends on the width it is read at, so it must be refused, not decided.
/// requires: true
/// ensures: (!0 + 1) < 1u8
pub fn contract_untyped_fold_overflow_is_refused() -> u8 {
    0
}

/// The equality form of the same shape: `(!0 + 2) == 1u8` was *verified* by
/// truncating the fold's scope-width `257` to the `u8`'s `1`, again for a program
/// rustc rejects as an overflow.
/// requires: true
/// ensures: (!0 + 2) == 1u8
pub fn contract_untyped_fold_overflow_equality_is_refused() -> u8 {
    0
}

/// The control: a fold that *fits* is width-independent and must still read.
///
/// `200 + 100` is `300` at any width holding it, so it widens exactly, and
/// `(x as u16) <= 200 + 100` holds for every `u8` `x`. Refusing the overflow must
/// not refuse this.
/// requires: x <= 100
/// ensures: (x as u16) <= 200 + 100
pub fn contract_fitting_fold_still_reads(x: u8) -> u8 {
    x
}

/// The valid control the same shape dropped: a complement *masked* to a value that
/// does not depend on the width is width-independent, so it widens exactly.
///
/// `!0 & 1` is `1` at any width, so `(x as u16) == (!0 & 1)` holds for `x == 1`.
/// The reader carried the masked result as an opaque constant and refused the
/// widening, dropping a valid postcondition.
/// requires: x == 1
/// ensures: (x as u16) == (!0 & 1)
pub fn contract_complement_mask_widens_exactly(x: u8) -> u8 {
    x
}

/// A shift by zero is the identity, so an opaque operand is unambiguous.
///
/// `!0 >> 0` is `!0`, and for a `u8` operand that is `255`, so `x == (!0 >> 0)`
/// holds at `x == 255`. The reader refused *every* right shift of an opaque
/// constant as sign-ambiguous, dropping this valid postcondition.
/// requires: x == 255
/// ensures: x == (!0 >> 0)
pub fn contract_complement_shift_by_zero_reads(x: u8) -> u8 {
    x
}

/// A division with a typed operand on one side is not sign-ambiguous.
///
/// `!0` is `-1` read as `i32`, but the *typed* `u8` `x` fixes the reading to
/// unsigned, so `!0` is `255` and `x / !0 == 0` for any `x < 255`. The reader saw
/// `!0`'s opaque sign and refused the division as untyped, dropping a valid
/// postcondition.
/// requires: x == 0
/// ensures: x / !0 == 0
pub fn contract_complement_division_with_typed_operand_reads(x: u8) -> u8 {
    x
}

/// A complement's *provisional* unsigned value must not be range-checked as if it
/// were a written literal.
///
/// `!(!1 + 1)` for an `i8` is valid Rust: `!1 + 1` is `-1`, and `!(-1)` is `0`, so
/// the value is `0`. The reader evaluates the fold unsigned (`255`) because its
/// type is not known until it meets the `i8`, and range-checking that *guess*
/// refused a contract naming it although no `255` is written. The fold now records
/// only its operands' envelopes, so the guess is not checked while a genuine
/// literal under the fold still is.
/// requires: y == 0
/// ensures: y == !(!1 + 1)
pub fn contract_opaque_fold_provisional_value_is_not_range_checked(y: i8) -> i8 {
    y
}

/// The negative control: a literal *under* the fold is still range-checked against
/// the type the complement meets, so `!128` for an `i8` is a `literal out of
/// range` error even though `!128` is `127`.
/// requires: y == 127
/// ensures: y == !128
pub fn contract_literal_under_complement_is_still_range_checked(y: i8) -> i8 {
    y
}

/// A `u128`-suffixed literal must be *refused*, not panicked.
///
/// The suffix carries width 128, and the range check that guards the literal
/// computes `1u128 << w`; at `w == 128` that shift panics in a debug build (it
/// wraps to a wrong `max` in release), and `smt::word` has no 128-bit width to
/// fall back on either. Both literals here are small, so the value is not the
/// problem -- the *type* is, and the contract has to be refused rather than
/// decided. This pins that the reader reports the function instead of taking the
/// run down.
/// requires: true
/// ensures: 0u128 == 0u128
pub fn contract_u128_suffix_literal_is_refused(x: u8) -> u8 {
    x
}

/// A *symbolic* masked operand keeps its own type, so a signed/unsigned pairing
/// is refused.
///
/// `x & 128` for a `u8` is still a `u8`: `&` does not change its operand's type,
/// and masking a symbolic value cannot make it inferable from a partner. Marking
/// the result untyped let `refuse_mixed_signedness` accept `(x & 128) == y` for a
/// signed `y`, a pairing rustc rejects (E0308), and give it a signed reading
/// instead of refusing it. The contract must not be decided.
/// requires: true
/// ensures: (x & 128) == y
pub fn contract_symbolic_mask_keeps_its_type(x: u8, y: i8) -> u8 {
    x
}

/// A *signed* constant mask keeps its signed type, so a signed/unsigned pairing is
/// refused.
///
/// `-1i8 & 1` is an `i8` in Rust even though its value is the small positive `1`:
/// the mask takes the typed operand's type, and `==` never coerces. So
/// `(-1i8 & 1) == y` for a `u8` `y` is `E0308` (`expected i8, found u8`). The
/// reader marked the constant result `Literal` (a width-independent value that may
/// widen), which hid the `i8`, and decided the comparison instead of refusing it.
/// The contract must not be verified.
/// requires: y == 1
/// ensures: (-1i8 & 1) == y
pub fn contract_signed_mask_vs_unsigned_is_refused(y: u8) -> u8 {
    y
}

/// The valid control for the signed mask: against a *signed* partner it reads.
///
/// `(-1i8 & 1) == y` for an `i8` `y` is well-typed, and `-1i8 & 1` is `1`, so the
/// equality holds at `y == 1`. The fix must keep the signed-mask shape readable
/// rather than refuse every mask with a signed operand.
/// requires: y == 1
/// ensures: (-1i8 & 1) == y
pub fn contract_signed_mask_with_signed_partner_reads(y: i8) -> i8 {
    y
}

/// The *unsigned* counterpart: a `u8` mask keeps its `u8` type, so a signed/unsigned
/// pairing is refused too.
///
/// The signed-mask fix only excluded a *signed* typed operand, which left this
/// symmetric hole open: `1u8 & 1` is a `u8` even though it computes `1`, so
/// `(1u8 & 1) == y` for an `i8` `y` is `E0308` (`expected u8, found i8`). The
/// reader still marked the constant `Literal` (the mark needed only "not signed")
/// and verified it. The contract must not be decided.
/// requires: y == 1
/// ensures: (1u8 & 1) == y
pub fn contract_unsigned_mask_vs_signed_is_refused(y: i8) -> i8 {
    y
}

/// The valid control for the unsigned mask: against an *unsigned* partner it reads.
///
/// `(1u8 & 1) == y` for a `u8` `y` is well-typed and holds at `y == 1`, so the
/// symmetric fix must not refuse every mask with an unsigned typed operand.
/// requires: y == 1
/// ensures: (1u8 & 1) == y
pub fn contract_unsigned_mask_with_unsigned_partner_reads(y: u8) -> u8 {
    y
}

/// A constant whose *type is fixed* may not meet a partner of another width.
///
/// `-1i8` is an `i8`, so `-1i8 < (x as i16)` is `E0308` (`expected i8, found
/// i16`) even though both operands are signed -- `refuse_mixed_signedness` sees
/// two signed operands and passes, so the *width* is the only remaining evidence.
/// `align_widths` used to resize the constant to the cast's width instead, erasing
/// it, and the contract was *verified*. It must not be decided.
/// requires: true
/// ensures: -1i8 < (x as i16)
pub fn contract_fixed_width_constant_vs_wider_cast_is_refused(x: u8) -> i16 {
    x as i16
}

/// A bare negation has no width of its own, so it *does* meet a wider operand.
///
/// The valid control for the width rule: `-1` is a negation of a bare literal, so
/// Rust infers its type from `(x as i16)` and `-1 < (x as i16)` is well-typed
/// (`-1` is less than any `x as i16`, so it holds for every `x`). The rule must
/// refuse only a *fixed* width, not every negation.
/// requires: true
/// ensures: -1 < (x as i16)
pub fn contract_bare_negation_meets_a_wider_operand(x: u8) -> i16 {
    x as i16
}

/// Two fixed-width constants of different widths may not be compared.
///
/// The both-constant counterpart: `1i8 == 1i16` is `E0308` in Rust. With neither
/// operand a bare literal there is no operand to infer a width from, so the
/// mismatch is the Rust error and the contract must not be decided.
/// requires: true
/// ensures: 1i8 == 1i16
pub fn contract_two_fixed_width_constants_are_refused() -> i16 {
    0
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

/// The signed-element read on the *postcondition* side, which is where the
/// missing sign record actually produced a false proof.
///
/// `bind_indexed_elem` recorded an element's signedness for the executor's seeds
/// but not for the parser, so `is_signed_name` said an `i8` element was unsigned.
/// `xs[0] >= 0` then read as an unsigned comparison, which is *always true*, and
/// this contract -- false at `xs[0] == i8::MIN` -- was reported verified. The
/// element's sign now reaches the parser, so it is refuted with the negative
/// element as the witness. The earlier `signed_slice_element_tripwire` did not
/// catch this: the body's own reading of `xs[0]` dominated its verdict, so the
/// bug hid behind a verdict that was already FAILED for another reason.
/// requires: xs.len() > 0
/// ensures: xs[0] >= 0
pub fn signed_slice_element_ensures_tripwire(xs: &[i8]) -> i8 {
    xs[0]
}

/// The same hole on the *symbolic* index chain.
///
/// `a[i]` is rewritten to an ite chain over the elements, and the chain was
/// inserted into the name table without the element's sign -- so `a[i] >= 0` over
/// an `i8` array read as unsigned and was proved for a body returning `a[i]`. It
/// is refuted now, with `a[i] == i8::MIN` as the witness.
/// requires: i < 4
/// ensures: a[i] >= 0
pub fn signed_array_chain_ensures_tripwire(a: [i8; 4], i: usize) -> i8 {
    a[i]
}

/// A struct literal builds a value whose *fields* the body can read back.
///
/// `Config { lo: 7, hi: 9 }` lowers to a struct-literal rvalue, which this
/// frontend used to leave `Unknown`: the literal's operands were parsed as an
/// array/tuple `Aggregate` and written under `Proj::Index`, while a field read
/// (`_1.0`) consults the *field* store. The two never met, so `c.lo` read
/// unknown and the contract was unreadable. The fields are printed in
/// declaration order, which is the order the `Field(N)` projections count in, so
/// the literal's `lo` is field `0`.
/// requires: true
/// ensures: ret == 7
pub fn struct_literal_reads_its_field() -> u8 {
    let c = Config { lo: 7, hi: 9 };
    c.lo
}

/// A struct literal's fields are read back by *declaration* order, not by the
/// order they were written in the source.
///
/// The literal is written `hi` first, but rustc prints the fields in declaration
/// order (`lo`, then `hi`), which is the order the `Field(N)` projections index.
/// The contract names `lo` and claims the constant, so it holds only if `lo` is
/// the first operand.
/// requires: true
/// ensures: ret == 7
pub fn struct_literal_order(a: u8) -> u8 {
    let c = Config { lo: 7, hi: a };
    c.lo
}

/// The tripwire for the struct-literal field *order*.
///
/// Same body as [`struct_literal_order`], but the contract claims the `hi`
/// operand. That is what `lo` would read if the parser keyed the operands by the
/// order they were *written* rather than by declaration order, so a reversed
/// model would prove this false contract. It must FAIL, with a witness in which
/// `a` is not `7`.
/// requires: true
/// ensures: ret == a
pub fn struct_literal_order_tripwire(a: u8) -> u8 {
    let c = Config { lo: 7, hi: a };
    c.lo
}

/// A reference to an argument is read back through the reference.
///
/// `let r = &a; *r` lowers to `_2 = &_1; _0 = copy (*_2)`. The deref is of a
/// local the run itself created, not of a `&T` argument, so the argument-only
/// `deref_ok` path did not apply and the read came back unknown. Modelling
/// `&place` as the place it addresses is what makes `*r` read `a`.
/// requires: a == 5
/// ensures: ret == 5
pub fn reference_reads_through(a: u8) -> u8 {
    let r = &a;
    *r
}

/// A reference *write* is seen by the target, so the borrow is not a copy.
///
/// `r` addresses `a`, and the write through `r` must be visible in `a`. If the
/// reference were modelled as a snapshot of `a`'s value rather than as the place
/// `a`, the read after the write would return the pre-write value and this
/// contract would be refuted. It must verify.
/// requires: true
/// ensures: ret == 7
pub fn reference_write_reaches_target() -> u8 {
    let mut a = 5u8;
    let r = &mut a;
    *r = 7;
    a
}

/// The tripwire for the reference-write direction.
///
/// Same body as [`reference_write_reaches_target`], but the contract claims the
/// value the target held *before* the write. That is the answer a snapshot model
/// gives, so this false contract is proved by exactly the bug. It must FAIL.
/// requires: true
/// ensures: ret == 5
pub fn reference_write_tripwire() -> u8 {
    let mut a = 5u8;
    let r = &mut a;
    *r = 7;
    a
}

/// `.len()` on an array argument is the length in its type.
///
/// `a.len()` on `a: [u8; 4]` lowers to `_3 = &_1; _2 = _3 as &[u8];
/// PtrMetadata(_2)`: the array is unsized to a slice and its metadata read. The
/// length is the type's constant, so it is exactly `4` and the contract has
/// something to agree with. Before this, the `PtrMetadata` named the slice local
/// with no `indexed` entry and read unknown.
/// requires: true
/// ensures: ret == 4
pub fn array_len_is_the_type_constant() -> usize {
    let a = [1u8, 2, 3, 4];
    a.len()
}

/// A struct argument reassigned wholesale carries its *fields* across.
///
/// `c = d` copies a value the frontend models as its parts, so the copy has to
/// move the fields or `c.lo` afterwards reads nothing. This is the readable half
/// of [`struct_reassign_then_field_read`]: the contract names `d.lo`, which is
/// what `c.lo` is after the assignment.
/// requires: d.lo == 3
/// ensures: ret == 3
pub fn struct_reassign_reads_new_field(mut c: Config, d: Config) -> u8 {
    c = d;
    c.lo
}

/// A `match` on an enum lowers to `switchInt(discriminant(m))`, and the tag is
/// an input this frontend now models.
///
/// `discriminant` reads a symbolic tag whose domain is the enum's arity, so the
/// three arms are reachable exactly as the type says and the `otherwise` arm --
/// which rustc lowers to `unreachable` for an exhaustive `match` -- is genuinely
/// unreachable. Every arm returns a value at most `2`, so the bound holds.
/// requires: true
/// ensures: ret <= 2
pub fn enum_match_is_bounded(m: Mode) -> u8 {
    match m {
        Mode::Off => 0,
        Mode::Idle => 1,
        Mode::Run => 2,
    }
}

/// The tag is the *only* thing a `match` reads, so a precondition on it selects
/// the arm.
///
/// This is the readable half of [`enum_match_tripwire`]: `m == Mode::Run` pins the
/// tag to `2`, which is the arm that returns `2`. A model that guessed the tag
/// (or read it as zero) would send every input down the `Off` arm and refute
/// this contract.
/// requires: m == Mode::Run
/// ensures: ret == 2
pub fn enum_match_selects_by_tag(m: Mode) -> u8 {
    match m {
        Mode::Off => 0,
        Mode::Idle => 1,
        Mode::Run => 2,
    }
}

/// The tripwire for the enum tag: an unconditional claim that only one arm's
/// value can satisfy.
///
/// Same body as [`enum_match_is_bounded`], but the contract claims the return is
/// always `2`. The `Off` and `Idle` arms make that false, so it must be refuted
/// -- and the witness must name the tag, which is the evidence the tag is
/// genuinely symbolic rather than a constant the model picked.
/// requires: true
/// ensures: ret == 2
pub fn enum_match_tripwire(m: Mode) -> u8 {
    match m {
        Mode::Off => 0,
        Mode::Idle => 1,
        Mode::Run => 2,
    }
}

/// A variant after an *explicit* discriminant takes rustc's value, not its
/// position.
///
/// `Gap` is `A, B = 3, C`, so rustc numbers `A`=0, `B`=3, `C`=4. A reader that
/// numbered by declaration order would call `C` the discriminant `1`, and a
/// contract saying `g == Gap::C` would then pin the tag to `1` -- the value of a
/// different variant. `match g { Gap::C => 7, _ => 0 }` compiles to
/// `switchInt(discriminant(g))` with the arm constant `4`, so the contract and
/// the arm only agree if the reader uses `4`.
///
/// The body returns `7` exactly when the tag is `4`, so the contract holds for
/// the real numbering and would fail for a positional one.
/// requires: g == Gap::C
/// ensures: ret == 2
pub fn enum_explicit_discriminant_selects_by_tag(g: Gap) -> u8 {
    match g {
        Gap::A => 0,
        Gap::B => 1,
        Gap::C => 2,
    }
}

/// The tripwire for explicit discriminants: the *positional* value must not be
/// what `Gap::C` means.
///
/// The same body, but the contract claims the return is `1` -- the `B` arm's
/// value. Under rustc's numbering `g == Gap::C` means tag `4`, which takes the
/// `C` arm and returns `2`, so the contract is false for every input and must
/// FAIL. A positional reader would call `Gap::C` the tag `1`, truncate the arm
/// constants to the arity's width, and land on the `B` arm -- proving this false
/// contract. Refuting it is the evidence the discriminant is rustc's value.
/// requires: g == Gap::C
/// ensures: ret == 1
pub fn enum_explicit_discriminant_tripwire(g: Gap) -> u8 {
    match g {
        Gap::A => 0,
        Gap::B => 1,
        Gap::C => 2,
    }
}

/// A variant *payload* is a symbolic input, read through the downcast.
///
/// `Msg::Data(x)` lowers to `_3 = copy ((_1 as Data).0)`, so the payload is read
/// as field 0 of variant 1. The contract names `m.Data`, which is bound to the
/// same variable, so `ret == m.Data` on the `Data` arm is a claim about one value
/// and not two that look alike.
/// requires: m == Msg::Data
/// ensures: ret == m.Data
pub fn enum_payload_reads_through(m: Msg) -> u8 {
    match m {
        Msg::Ping => 0,
        Msg::Data(x) => x,
        Msg::Stop => 255,
    }
}

/// The tripwire for the payload: the *wrong* variant's payload.
///
/// `m.Ping` is a unit variant, so it has no payload to read. The contract must be
/// refused rather than bound to a fabricated value -- a model that bound every
/// variant to the same payload would prove this false contract.
/// requires: true
/// ensures: ret == m.Ping
pub fn enum_payload_tripwire(m: Msg) -> u8 {
    match m {
        Msg::Ping => 0,
        Msg::Data(x) => x,
        Msg::Stop => 255,
    }
}

/// A *locally constructed* variant has a known tag, so its `match` is decided
/// rather than symbolic.
///
/// `let m = Mode::Idle;` lowers to `_1 = Mode::Idle; _2 = discriminant(_1)`, and
/// `Mode::Idle` is a path constant. Resolving it to the enum's declaration index
/// is what makes the tag a *constant* `1` here, so only the `Idle` arm is
/// reachable and the contract is decided rather than left as a coverage gap.
/// requires: true
/// ensures: ret == 1
pub fn enum_constructed_locally() -> u8 {
    let m = Mode::Idle;
    match m {
        Mode::Off => 0,
        Mode::Idle => 1,
        Mode::Run => 2,
    }
}

/// The tripwire for construction: the wrong variant's arm.
///
/// Same body as [`enum_constructed_locally`], but the contract claims the
/// `Off` arm ran. A model that resolved `Mode::Idle` to `Off` -- or to a
/// symbolic tag -- would prove this, so refuting it is the evidence the
/// discriminant is the declaration index and not a guess.
/// requires: true
/// ensures: ret == 0
pub fn enum_constructed_locally_tripwire() -> u8 {
    let m = Mode::Idle;
    match m {
        Mode::Off => 0,
        Mode::Idle => 1,
        Mode::Run => 2,
    }
}

/// A constructed variant's payload is read through the downcast.
///
/// `Msg::Data(9)` lowers to a construction of tag `1` with payload `9` written
/// into field 0, and the match's `Data(x)` arm reads that field. The contract
/// names the constant, so it is decided.
/// requires: true
/// ensures: ret == 9
pub fn enum_constructed_payload_reads_through() -> u8 {
    let m = Msg::Data(9);
    match m {
        Msg::Ping => 0,
        Msg::Data(x) => x,
        Msg::Stop => 255,
    }
}

/// A user enum whose variant names collide with `Option`'s.
///
/// `Shadow` is `Some, None` -- but here they are *this* enum's variants, not
/// `Option`'s, and `Shadow::Some` is tag `0`. A reader that resolved a variant
/// name to the built-in `Option` numbering before consulting the declared layout
/// would read `Shadow::Some` as `Option`'s `Some`, which is tag `1`, and the
/// contract and the `match` arm would then disagree about which variant `s` is.
pub enum Shadow { Some, None }

/// The contract names `Shadow::Some`, which is tag `0` for this enum.
/// requires: s == Shadow::Some
/// ensures: ret == 0
pub fn enum_user_variant_not_option(s: Shadow) -> u8 {
    match s {
        Shadow::Some => 0,
        Shadow::None => 1,
    }
}

/// The tripwire: `Option`'s numbering for `Some` is `1`, so a reader that used it
/// would pin the tag to `1` -- the `None` arm -- and prove this false contract.
/// requires: s == Shadow::Some
/// ensures: ret == 1
pub fn enum_user_variant_not_option_tripwire(s: Shadow) -> u8 {
    match s {
        Shadow::Some => 0,
        Shadow::None => 1,
    }
}

/// The construction path for the same collision: `let s = Shadow::Some;`.
///
/// A local construction resolves the variant name through the same table a
/// contract does. `Shadow::Some` is tag `0` here, so the `Some` arm runs and the
/// return is `0`. A reader that took the built-in `Option` numbering for the
/// qualified name would build the tag `1` -- the `None` arm -- and the run would
/// report `1` instead of `0`.
/// requires: true
/// ensures: ret == 0
pub fn enum_user_variant_not_option_constructed() -> u8 {
    let s = Shadow::Some;
    match s {
        Shadow::Some => 0,
        Shadow::None => 1,
    }
}

/// The tripwire for the constructed collision: `ret == 1` is what the built-in
/// `Option` numbering produces, and it is false for every input.
/// requires: true
/// ensures: ret == 1
pub fn enum_user_variant_not_option_constructed_tripwire() -> u8 {
    let s = Shadow::Some;
    match s {
        Shadow::Some => 0,
        Shadow::None => 1,
    }
}

/// A *qualified* standard construction resolves to the same tag as the
/// unqualified one.
///
/// rustc prints a standard construction with its generic arguments:
/// `let o: Option<u8> = Option::<u8>::Some(9);` lowers to
/// `_1 = Option::<u8>::Some(const 9_u8); _2 = discriminant(_1)` with
/// `switchInt(move _2) -> [0: …, 1: …]`. No source file declares a layout for
/// `Option`, so a reader that resolves a qualified name only through a declared
/// layout finds none and refuses the construction -- losing a shape the
/// unqualified spelling handles. The `::<u8>` is part of the spelling, not the
/// variant, so it is dropped before the qualifier is read.
/// requires: true
/// ensures: ret == 9
pub fn option_qualified_some_payload() -> u8 {
    let o: Option<u8> = Option::<u8>::Some(9);
    match o {
        Option::Some(v) => v,
        Option::None => 0,
    }
}

/// The tripwire for the qualified standard construction: `None` is tag `0` and
/// takes the other arm, so the payload `9` is never returned.
/// requires: true
/// ensures: ret == 0
pub fn option_qualified_some_payload_tripwire() -> u8 {
    let o: Option<u8> = Option::<u8>::Some(9);
    match o {
        Option::Some(v) => v,
        Option::None => 0,
    }
}

/// An enum whose variants carry trailing line comments.
///
/// `B = 3, // special` puts the comma *before* the comment, so a reader that
/// trims a trailing comma off the raw line no longer sees a comma at all and
/// hands `3, // special` to the discriminant parser, which rejects it. The whole
/// layout is then dropped and a contract naming any variant is refused. The
/// comment is not part of the variant, so stripping it first leaves `B = 3,` and
/// the layout is read.
pub enum Commented {
    A, // first
    B = 3, // special
    C,
}

/// The contract names `Commented::C`, which is tag `4` (it follows `B = 3`).
/// requires: c == Commented::C
/// ensures: ret == 2
pub fn enum_trailing_comment_keeps_the_layout(c: Commented) -> u8 {
    match c {
        Commented::A => 0,
        Commented::B => 1,
        Commented::C => 2,
    }
}

/// The tripwire: `Commented::C` is not the `B` arm, so `ret == 1` is false.
/// requires: c == Commented::C
/// ensures: ret == 1
pub fn enum_trailing_comment_tripwire(c: Commented) -> u8 {
    match c {
        Commented::A => 0,
        Commented::B => 1,
        Commented::C => 2,
    }
}

/// A `match` on a *standard-library* enum **argument**.
///
/// `Option` and `Result` are read by real functions (`checked_add` returns
/// `Option<u8>`; `?` threads a `Result`), but no source file declares them, so an
/// argument of one of those types had no layout: the tag was never seeded and the
/// `switchInt` on it came back an *unmodelled switch discriminant*. A declared
/// enum argument (`Mode`) and a locally constructed `Option` both worked; the
/// argument form is the one the reader has to know without a declaration.
/// The contract is true for every input, so it must VERIFY -- `None` gives `0`
/// and `Some` gives `1`, and both are `<= 1`.
/// requires: true
/// ensures: ret <= 1
pub fn option_arg_match(x: Option<u8>) -> u8 {
    match x {
        Some(_) => 1,
        None => 0,
    }
}

/// The tripwire for the standard-enum argument: the body returns `1` for `Some`
/// and `0` for `None`, so `ret == 0` is false whenever the caller passes `Some`.
/// A model that seeded no tag would not reach this -- it refused -- but one that
/// seeded a *constant* tag would take one arm always and could prove this.
/// requires: true
/// ensures: ret == 0
pub fn option_arg_match_tripwire(x: Option<u8>) -> u8 {
    match x {
        Some(_) => 1,
        None => 0,
    }
}

/// The `Result` half: `Ok` is tag `0` and `Err` is tag `1`, and the two type
/// arguments are the payloads in order, so `Ok`'s payload is a `u8` and `Err`'s is
/// a `u16`. The contract is true for both arms.
/// requires: true
/// ensures: ret <= 1
pub fn result_arg_match(r: Result<u8, u16>) -> u8 {
    match r {
        Ok(_) => 0,
        Err(_) => 1,
    }
}

/// The tripwire: `Err` takes the second arm, so `ret == 0` is false when the
/// caller passes `Err`.
/// requires: true
/// ensures: ret == 0
pub fn result_arg_match_tripwire(r: Result<u8, u16>) -> u8 {
    match r {
        Ok(_) => 0,
        Err(_) => 1,
    }
}

/// The `Option` payload read through the argument: `Some`'s payload is the type
/// argument, so `Option<u8>::Some` carries a `u8`. The body's downcast read
/// `((_1 as Some).0)` must name the same seeded payload variable the contract's
/// `x.Some` does. A tautology like `ret <= 255` would hold even if the payload
/// came back unconstrained, so it would pin nothing; `ret <= x.Some` fails on the
/// `Some` arm whenever the body returns anything but the seeded payload.
/// requires: true
/// ensures: ret <= x.Some
pub fn option_arg_payload_passthrough(x: Option<u8>) -> u8 {
    match x {
        Some(v) => v,
        None => 0,
    }
}

/// The tripwire: the contract claims the payload is one more than it is, so the
/// `Some` arm is false for every input -- the payload is read, not a free
/// variable the contract could make true.
/// requires: true
/// ensures: ret == x.Some + 1
pub fn option_arg_payload_tripwire(x: Option<u8>) -> u8 {
    match x {
        Some(v) => v,
        None => 0,
    }
}

// ---------------------------------------------------------------------------
// A cast in a *contract*: `x as u32`. The body has modelled `as` for a while
// (it is what lets a narrow argument meet a wide return), but the contract
// language had no cast at all, so any contract that related the two was
// unreadable -- `ret == x as u32` came back `cannot read contract`. A cast in a
// contract has to *extend*, not reinterpret: `-1i8 as i16` is `-1`, not `255`.
// An unknown source sign is a refusal, the same call the body makes, because
// guessing it is how `-1i8 as i16 == 255` becomes a reachable false proof.

/// A widening cast of an *unsigned* source zero-fills, so `x as u32` is `x`.
/// requires: true
/// ensures: ret == x as u32
pub fn contract_cast_widens_unsigned(x: u8) -> u32 {
    x as u32
}

/// The tripwire: the same widening, but the contract names a value one too high,
/// so it is false for every input -- the cast is read, not a free variable.
/// requires: true
/// ensures: ret == (x as u32) + 1
pub fn contract_cast_widens_unsigned_tripwire(x: u8) -> u32 {
    x as u32
}

/// A widening cast of a *signed* source sign-extends, so `x as i32` is the same
/// signed value. The contract's `x as i32` and the body's `x as i32` must both
/// sign-extend; if either zero-filled, `requires: x == -1; ensures: ret == -1`
/// would be refuted at `-1` (the body would return `255`).
/// requires: x == -1
/// ensures: ret == -1
pub fn contract_cast_widens_signed(x: i8) -> i32 {
    x as i32
}

/// The tripwire that separates sign-extension from zero-filling. Rust sign-extends
/// through a widening cast even when the *target* is unsigned: `-1i8 as u16` is
/// `65535`, not the zero-extended `255`. A contract cast that zero-filled would
/// name `255`, and the true entry below (`ret == 65535`) would be refuted instead
/// of proved -- so this pair pins the direction.
/// requires: x == -1
/// ensures: ret == 255
pub fn contract_cast_signed_to_unsigned_tripwire(x: i8) -> u16 {
    x as u16
}

/// The true half of the pair above: `-1i8 as u16` sign-extends to `65535`.
/// requires: x == -1
/// ensures: ret == 65535
pub fn contract_cast_signed_to_unsigned(x: i8) -> u16 {
    x as u16
}

/// A narrowing cast keeps the low bits: `x as u8` drops the high byte. The body
/// and the contract must agree, so `ret == x as u8` is the identity here.
/// requires: true
/// ensures: ret == x as u8
pub fn contract_cast_narrows(x: u16) -> u8 {
    x as u8
}

/// The tripwire for narrowing pins *which* bits are kept: `256` is `0x100`, so
/// `256 as u8` is `0` (the low byte), not `1`. A model that kept the wrong byte,
/// or read the cast as a free variable, could make `ret == 1` true.
/// requires: x == 256
/// ensures: ret == 1
pub fn contract_cast_narrows_tripwire(x: u16) -> u8 {
    x as u8
}

/// A cast chain applies left to right, and each step's source sign is the
/// previous step's target sign. `x as u16 as u32` is two zero-fills, which is `x`.
/// requires: true
/// ensures: ret == x as u16 as u32
pub fn contract_cast_chain(x: u8) -> u32 {
    x as u16 as u32
}

/// The tripwire: the chain is a value, not a free variable, so naming it one too
/// high is false for every input.
/// requires: true
/// ensures: ret == (x as u16 as u32) + 1
pub fn contract_cast_chain_tripwire(x: u8) -> u32 {
    x as u16 as u32
}

/// A cast in a contract is a *value* the order can be asked about, not only a
/// spelling that can be equated with the return. `x as i16` for a `u8` `x` is
/// non-negative, because zero-filling a `u8` into a wider signed type cannot set
/// the sign bit. The comparison is therefore decided on the cast's value rather
/// than refused as an unknown sign, which is what the equality entries above do
/// not show: they only ever meet the cast with `==`.
/// requires: true
/// ensures: (x as i16) >= 0
pub fn contract_cast_relational_nonneg(x: u8) -> u8 {
    x
}

/// The same cast against the upper bound: a `u8` zero-fills into `i16` in
/// `[0, 255]`, so `(x as i16) < 256` holds for every input. Pinned with the
/// entry above so both ends of the widened range are exercised, and neither is a
/// constant the reader could have folded to the answer.
/// requires: true
/// ensures: (x as i16) < 256
pub fn contract_cast_relational_lt_width(x: u8) -> u8 {
    x
}

/// A *signed* source sign-extends into the wider signed target, so `y as i16` for
/// an `i8` `y` is `<= 127` -- the top of the source's range, sign-extended. A
/// model that zero-filled would place `-1i8 as i16` at `255`, and this contract
/// would be refuted at `y == -1`.
/// requires: true
/// ensures: (y as i16) <= 127
pub fn contract_cast_relational_signed_bound(y: i8) -> i8 {
    y
}

/// The tripwire for the two `>= 0` claims above: the *signed* source is not
/// non-negative, so `(y as i16) >= 0` is false at every negative `y` and the
/// function must be refuted. A reader that dropped the sign of the source and
/// treated the cast as unsigned would prove this, which is the false proof the
/// pair exists to forbid.
/// requires: true
/// ensures: (y as i16) >= 0
pub fn contract_cast_relational_signed_nonneg_tripwire(y: i8) -> i8 {
    y
}

/// The tripwire for the widened upper bound: an `unsigned` source is *not* always
/// positive, so `(x as i16) > 0` is false at `x == 0` and the function must be
/// refuted. Together with `..._lt_width` this pins that the reader knows the
/// widened value's true range rather than accepting any comparison about it.
/// requires: true
/// ensures: (x as i16) > 0
pub fn contract_cast_relational_positive_tripwire(x: u8) -> u8 {
    x
}

/// `a.wrapping_add(b)` is the method-call spelling of the wrapping add the
/// contract language already models as `a + b`, so the two must denote one term.
/// The precondition is a *relation* between the two inputs, which is the shape the
/// reader has to reason about rather than fold, and the body computes exactly the
/// term the postcondition names.
/// requires: x < y
/// ensures: ret == x.wrapping_add(y)
pub fn contract_wrapping_add_reads(x: u8, y: u8) -> u8 {
    x.wrapping_add(y)
}

/// The tripwire: the wrapping add is a *value*, not a free variable, so naming it
/// one too high is false for every input. Without this, a reader that treated
/// `x.wrapping_add(y)` as an uninterpreted call would prove the true entry above
/// and this one too.
/// requires: x < y
/// ensures: ret == x.wrapping_add(y).wrapping_add(1)
pub fn contract_wrapping_add_is_a_value_tripwire(x: u8, y: u8) -> u8 {
    x.wrapping_add(y)
}

/// The same sugar for `-` and `*`, and the chained form: the postfix applies left
/// to right, so `x.wrapping_sub(1).wrapping_mul(2)` is `(x - 1) * 2` computed with
/// wrapping at eight bits. The body writes the same wrapping operations, which
/// pins that the two spellings denote one term on every input -- including the
/// `x == 0` case, where the plain operators would instead panic on overflow.
/// requires: true
/// ensures: ret == x.wrapping_sub(1).wrapping_mul(2)
pub fn contract_wrapping_sub_mul_chain_reads(x: u8) -> u8 {
    x.wrapping_sub(1).wrapping_mul(2)
}

/// And the agreement with the *plain* operators where no overflow can occur: in
/// `1..=100` the wrapping and the checked operations coincide, so the body may
/// write `(x - 1) * 2` and the contract's sugar must denote the same value. This
/// is the entry that separates "the sugar is the operator" from "the sugar is an
/// uninterpreted call", which the entry above cannot: there the body is wrapping
/// too, so a reader that modelled both as a fresh variable would still agree.
/// requires: x >= 1 && x <= 100
/// ensures: ret == x.wrapping_sub(1).wrapping_mul(2)
pub fn contract_wrapping_agrees_with_the_plain_operators(x: u8) -> u8 {
    (x - 1) * 2
}

/// `wrapping_neg` is `0 - x` at the operand's width, and it is legal for an
/// *unsigned* receiver where the unary `-` is not: `(1u8).wrapping_neg()` is
/// `255`. A reader that reused the unary negation's signed-only rule would refuse
/// this, so the entry pins that the sugar is read as the wrapping operator it is.
/// requires: true
/// ensures: ret == (1u8).wrapping_neg()
pub fn contract_wrapping_neg_on_unsigned_reads() -> u8 {
    255
}

/// And on a signed receiver: `y.wrapping_neg()` for an `i8` is `0 - y`, which at
/// `y == i8::MIN` is `i8::MIN` again rather than an overflow, so the body's
/// `wrapping_neg` and the contract's are one value.
/// requires: true
/// ensures: ret == y.wrapping_neg()
pub fn contract_wrapping_neg_on_signed_reads(y: i8) -> i8 {
    y.wrapping_neg()
}

/// The deliberate difference from `+`: a *constant* `+` that overflows its type is
/// refused (`200u8 + 100u8` is a rustc error), but `200u8.wrapping_add(100u8)` is
/// a legal program whose value is `44`. So the sugar must not run the overflow
/// fold -- it takes the engine's wrapping value, which is what Rust computes. This
/// entry fails if the reader refuses the shape, and is refuted if it computes
/// `300`.
/// requires: true
/// ensures: ret == 200u8.wrapping_add(100u8)
pub fn contract_wrapping_add_of_constants_wraps() -> u8 {
    44
}

/// The operands' literals are still range-checked against the type they meet:
/// `x.wrapping_add(300)` is a rustc error for its `300`, so the shape is refused
/// rather than decided, even though the *method* is a wrapping one. The wrapping
/// semantics excuse the overflow of the *result*, not an out-of-range literal.
/// requires: true
/// ensures: ret == x.wrapping_add(300)
pub fn contract_wrapping_add_of_an_out_of_range_literal_is_refused(x: u8) -> u8 {
    x
}

/// A receiver whose type is not known is refused: Rust rejects
/// `1.wrapping_add(2)` with `E0689` ("can't call method on ambiguous numeric type
/// `{integer}`"), so the reader must not silently give the bare literal the
/// scope's width and decide the shape.
/// requires: true
/// ensures: ret == 1.wrapping_add(2)
pub fn contract_wrapping_add_on_an_untyped_receiver_is_refused(x: u8) -> u8 {
    x
}

/// Unary `-` binds *tighter* than `as` in Rust, so `-x as u8` is `(-x) as u8`,
/// not `-(x as u8)`. The two readings agree on the value here — negation and
/// truncation commute — but not on the *type*: Rust's is `u8`, the other is
/// signed. This precondition is satisfiable only under the unsigned reading
/// (`x == 1` gives `255`, which is `> 127`); a signed `i8` is never `> 127`, so
/// reading the negation outside the cast makes the function *vacuous*. The body
/// returns `1` unconditionally, so it verifies exactly when the precondition is
/// satisfiable.
/// requires: -x as u8 > 127
/// ensures: ret == 1
pub fn contract_neg_binds_tighter_than_cast(x: i8) -> u8 {
    1
}

/// The value reading, which both parses agree on (negation and truncation
/// commute), so this guards against a fix that broke the *value* while fixing the
/// type: at `x == -5`, `-x` is `5`, and `5 as u8` is `5`.
/// requires: x == -5
/// ensures: ret == -x as u8
pub fn contract_neg_cast_value(x: i8) -> u8 {
    -x as u8
}

/// The tripwire, and the direction that matters: `255 < 127` is *false* on the
/// unsigned `u8` that Rust produces, so the tool must refute this. Under the
/// signed reading (`-1 < 127`) it would be *true* and the function would verify —
/// a false proof. That is the failure the precedence bug produced, so this entry
/// failing to refute is the alarm.
/// requires: x == 1
/// ensures: -x as u8 < 127
pub fn contract_neg_binds_tighter_than_cast_tripwire(x: i8) -> u8 {
    1
}

/// Unary `!` on a *value* is bitwise NOT, and binds *tighter* than `==`, so
/// `!x == 5` is `(!x) == 5` (`x == 250`), not `!(x == 5)` (`x != 5`). The two are
/// different predicates, so reading it the second way is a wrong verdict, not a
/// refusal. The body returns `x`, so with Rust's reading the postcondition holds
/// and the function verifies; with the predicate reading the tool would refute it
/// at `x == 0`.
/// requires: !x == 5
/// ensures: ret == 250
pub fn contract_bang_binds_tighter_than_eq(x: u8) -> u8 {
    x
}

/// A control for the entry above, not a reverse discriminator. The two readings of
/// `!x == 5` are `x == 250` (Rust) and `x != 5` (the bug); the second is *broader*,
/// so it can only refute things the first verifies, never verify something the
/// first refutes — there is no false-proof direction here. What this entry does is
/// prove the tool is not simply verifying everything under that precondition: the
/// body returns `x`, so `ret == 249` is false at the only input Rust admits
/// (`x == 250`) and the tool must refute it under *both* readings.
/// requires: !x == 5
/// ensures: ret == 249
pub fn contract_bang_binds_tighter_than_eq_control(x: u8) -> u8 {
    x
}

/// A bare `!x` on an integer is bitwise NOT: for `u8`, `!0` is `255`. It used to
/// be unreadable, which dropped the obligation rather than checking it.
/// requires: x == 0
/// ensures: ret == !x
pub fn contract_bang_is_bitwise_not(x: u8) -> u8 {
    !x
}

/// A predicate `!` still negates: `!(x == 8)` is `x != 8`, so the guard holds at
/// `x == 7` and the function verifies. This is the shape that must *not* break
/// when value-level `!` is added.
/// requires: x == 7 && !(x == 8)
/// ensures: ret == 1
pub fn contract_bang_still_negates_a_predicate(x: u8) -> u8 {
    1
}

/// The false-proof tripwire for an *untyped* constant in an equality.
///
/// `!0` has no type of its own. Rust types an untyped constant as `i32`, so `!0`
/// is `-1` and `!0 == 255` is `false` -- the postcondition holds for no input.
/// The reader used to carry the complement as a bit pattern at the scope's width,
/// build `255u8 == 255`, and *verify* this. With the refusal it is `skipped`.
/// requires: true
/// ensures: !0 == 255
pub fn contract_untyped_complement_equality_is_refused(x: u8) -> u8 {
    x
}

/// The control: a typed operand fixes the reading, so `!0` becomes a `u8` and
/// `x == !0` is exactly `x == 255` -- what Rust means. This must still read and
/// verify, so the refusal above is not a blanket ban on `!` in a comparison.
/// requires: x == !0
/// ensures: ret == 255
pub fn contract_complement_of_literal_with_typed_partner_reads(x: u8) -> u8 {
    x
}

/// The false-proof tripwire for a complement of an *out-of-range* literal.
///
/// `!128` for an `i8` is a rustc `literal out of range for i8` error: `128` does
/// not fit a signed eight-bit type, even though the *complement's* value `127`
/// does. The reader built `!128` as the constant `127`, marked it `Opaque`, and
/// let the resize truncate it with no check, so `y <= !128` read as `y <= 127`
/// (`i8::MAX`) and *verified* -- a false proof on a program rustc rejects. It must
/// be refused, not decided.
/// requires: true
/// ensures: y <= (!128)
pub fn contract_complement_of_out_of_range_literal_is_refused(y: i8) -> i8 {
    y
}

/// The control: `!127` fits an `i8` (`127` is `i8::MAX`), so the complement is a
/// legal `i8` and the comparison must still read. This keeps the refusal above
/// drawn at the range, not at `!`.
/// requires: true
/// ensures: y <= (!127)
pub fn contract_fitting_complement_still_reads(y: i8) -> i8 {
    y
}

/// The control for the *width*: `!128` against an `i16` is legal (`128` fits an
/// `i16`), so the same complement that is refused for an `i8` must read here. A
/// fix that refused every `!`-of-`128` regardless of the partner width would fail
/// this.
/// requires: true
/// ensures: b <= (!128)
pub fn contract_complement_reads_at_a_wider_operand(b: i16) -> i16 {
    b
}

/// Unary `-` on an *unsigned* name is a rustc error (`E0600: cannot apply unary
/// operator `-` to type `u8``). The reader modelled it as `0 - x`, a value Rust
/// never produces, so the shape is refused rather than decided.
/// requires: -x >= 0
/// ensures: ret == 0
pub fn contract_unsigned_negation_is_refused(x: u8) -> u8 {
    0
}

/// The control: a negation of a *signed* name is legal and must still read, so the
/// refusal above is not a blanket ban on unary `-`.
/// requires: x == -5
/// ensures: ret == -x as u8
pub fn contract_signed_negation_still_reads(x: i8) -> u8 {
    -x as u8
}

// ---------------------------------------------------------------------------
// Negating a *constant* is checked against the value it denotes, not the written
// magnitude, so a negation that overflows its own type is refused.
//
// `i8::MIN` is the bit pattern `128` and the value `-128`. The reader's range
// check read the bit pattern -- the same `128` the *legal* literal `128i8` has --
// so the negation passed and was recorded as the in-range `-128`, and the reader
// *decided* `y == -(i8::MIN)` on a program rustc rejects ("attempt to negate
// `i8::MIN`, which would overflow"). `3 << 7` at eight bits wraps to the same bit
// pattern, so `-(3 << 7)` was decided too. Only a pristine literal is exempt,
// because there the negation is what makes the magnitude legal (`-128i8` reads).
//
// These are `skipped`, not `verified` and not `failed`.
/// requires: true
/// ensures: y == -(i8::MIN)
pub fn contract_negation_of_min_is_refused(y: i8) -> i8 {
    y
}

/// The same overflow reached through a shift that wraps to `i8::MIN`'s pattern,
/// so the check is on the *value* and not on the `i8::MIN` spelling.
/// requires: true
/// ensures: y == -(3 << 7)
pub fn contract_negation_of_wrapping_shift_is_refused(y: i8) -> i8 {
    y
}

/// The control: negating `i8::MAX` is in range and must still read, so the
/// refusal above is pinned to the overflow and not to a negation of a bound.
/// requires: y == -127
/// ensures: ret == -y as i8
pub fn contract_negation_of_max_still_reads(y: i8) -> i8 {
    -y
}

/// A shift *amount* may be a constant expression, not only a bare literal:
/// `x >> 1 + 1` is `x >> 2` in Rust. The reader accepted only a raw literal, so
/// this shape was unreadable -- a dropped obligation on something rustc compiles.
/// The body shifts by `2`, so this verifies exactly when the amount folds.
/// requires: x == 8
/// ensures: ret == x >> 1 + 1
pub fn contract_shift_amount_is_folded(x: u8) -> u8 {
    x >> 2
}

/// The same folding on the *body* side: the amount `1 + 1` is constant, so the
/// body must lower it to a constant shift rather than a barrel shifter. It was
/// classified symbolic, which left the query undecided; folding it makes the
/// function prove.
/// requires: x == 8
/// ensures: ret == 2
pub fn body_shift_amount_is_folded(x: u8) -> u8 {
    x >> 1 + 1
}

/// A divisor of *zero* must be refused however it is spelled. `1 - 1` folds to
/// `0`, and checking only for a bare `0` literal let it through, so the reader
/// built `srem(x, 0)` -- an undefined operation -- and returned a definite verdict
/// from it. Refusing the folded zero turns that into a visible skip.
/// requires: x == 3
/// ensures: ret == x % (1 - 1)
pub fn contract_divisor_zero_is_folded(x: u8) -> u8 {
    x % 3
}

/// A *constant, non-zero* divisor in folded form still reads and models exactly:
/// `4 / (1 + 1)` is `4 / 2` is `2`, the same as the body.
/// requires: x == 4
/// ensures: ret == x / (1 + 1)
pub fn contract_divisor_folded_is_read(x: u8) -> u8 {
    x / 2
}

/// Value-level `!` binds tighter than a cast, so `!x as u8` is `(!x) as u8`: at
/// `x == 0` that is `255`. Reading it as `!(x as u8)` would make the `!` a predicate
/// negation and this would not parse at all, so the entry pins the binding.
/// requires: x == 0
/// ensures: ret == !x as u8
pub fn contract_bang_binds_tighter_than_a_cast(x: u8) -> u8 {
    !x
}

/// Value-level `!` binds tighter than `&`, so `!x & 1` is `(!x) & 1`: at `x == 0`
/// that is `255 & 1 == 1`. A reading that let `&` bind first would compute
/// `!(x & 1)`, which is `254` here.
/// requires: x == 0
/// ensures: ret == !x & 1
pub fn contract_bang_binds_tighter_than_and(x: u8) -> u8 {
    !x & 1
}

/// A parenthesis does not turn `!` into a predicate negation: `!(x + 1)` holds
/// *arithmetic*, so `!(x + 1) == 5` is `(!(x + 1)) == 5`, i.e. `x == 249`, not the
/// negation of `(x + 1) == 5` (which is not even well-typed). Contrast
/// `contract_bang_still_negates_a_predicate`, where the parenthesis holds a
/// *comparison* and the `!` does negate.
/// requires: x == 249
/// ensures: !(x + 1) == 5
pub fn contract_bang_paren_arithmetic_is_a_value(x: u8) -> u8 {
    0
}

// ---------------------------------------------------------------------------
// Radix literals: `0x`, `0b`, `0o`.
//
// The tokenizer read every numeric literal as decimal. The digit run stopped at
// the `x` of `0xFF` and the rest was skipped as a type suffix, so the value was
// `0` -- and a wrong value in a precondition is a *false proof*, not a refusal:
// `requires: x == 0xFF` became `x == 0`, so `ensures: ret == 0` was proved for a
// function returning `255`. These entries pin the value each radix reads, and the
// control pins that the fixed value is *not* the truncated one.

/// A hex literal reads at radix 16: `0xFF` is `255`. The body returns the argument
/// unchanged, so `ret == 255` holds only under the correct reading; the truncated
/// `x == 0` reading refutes it.
/// requires: x == 0xFF
/// ensures: ret == 255
pub fn contract_hex_literal_is_255(x: u8) -> u8 {
    x
}

/// A binary literal reads at radix 2: `0b1010` is `10`, not `0`.
/// requires: x == 0b1010
/// ensures: ret == 10
pub fn contract_binary_literal_is_ten(x: u8) -> u8 {
    x
}

/// An octal literal reads at radix 8: `0o17` is `15`, not `0`.
/// requires: x == 0o17
/// ensures: ret == 15
pub fn contract_octal_literal_is_fifteen(x: u8) -> u8 {
    x
}

/// Underscores separate digits in any radix: `0xFF_FF` is `65535`.
/// requires: x == 0xFF_FF
/// ensures: ret == 65535
pub fn contract_hex_underscore_is_65535(x: u16) -> u16 {
    x
}

/// A hex literal with a type suffix is still that value: `0xFFu8` is `255`.
/// requires: x == 0xFFu8
/// ensures: ret == 255
pub fn contract_hex_with_suffix_is_255(x: u8) -> u8 {
    x
}

/// The control: the *truncated* reading is `0`, so `ret == 0` is false for a body
/// that returns `x` under `x == 0xFF`. This must be **refuted**; if the literal is
/// mis-read as `0`, the precondition becomes `x == 0` and this is "proved" -- the
/// false proof the fix removes.
/// requires: x == 0xFF
/// ensures: ret == 0
pub fn contract_hex_literal_is_not_zero_control(x: u8) -> u8 {
    x
}

/// A radix literal is a *value* in arithmetic too, not only a bare atom: `0x10 + 1`
/// is `17`, and the reader must fold it the same way it folds a decimal.
/// requires: x == 0x10 + 0x01
/// ensures: ret == 17
pub fn contract_hex_arithmetic_is_folded(x: u8) -> u8 {
    x
}

/// A radix literal as a *shift amount*: `x >> 0x1` is `x >> 1`. The shift-amount
/// path folds the operand, so the literal has to be a constant there too.
/// requires: x == 4
/// ensures: ret == x >> 0x1
pub fn contract_hex_shift_amount(x: u8) -> u8 {
    x >> 1
}

/// A radix literal in a mask: `x & 0x0F` keeps the low nibble. At `x == 0xAB`
/// that is `0x0B == 11`.
/// requires: x == 0xAB
/// ensures: ret == x & 0x0F
pub fn contract_hex_mask_keeps_low_nibble(x: u8) -> u8 {
    x & 0x0F
}

/// A *negative* radix literal: `-0xFF` is `-255`, so the prefix binds before the
/// value is negated. The body returns `x` at `x == -255`.
/// requires: x == -0xFF
/// ensures: ret == -255
pub fn contract_negative_hex_literal(x: i16) -> i16 {
    x
}

/// An uppercase prefix is the same radix: `0XFF` is `255`.
/// requires: x == 0XFF
/// ensures: ret == 255
pub fn contract_uppercase_hex_prefix(x: u8) -> u8 {
    x
}

// ---------------------------------------------------------------------------
// A literal that does not fit the operand's *signed* width.
//
// `128` for an `i8` is `0x80`, the bit pattern of `-128`, so a reader that asks
// only "does this fit in eight unsigned bits?" accepts it and reads `x <= 128` as
// `x <= -128`. rustc rejects `x <= 128` for an `i8` ("literal out of range"), and
// the wrong reading is a *false proof*: `requires: x <= 128` with `ensures: x !=
// 127` held, because `-128..=127` excludes nothing that `<= -128` admits. The same
// holds for a negation: `-129` for an `i8` wraps to `127` at eight bits.

/// `128` does not fit an `i8` (it is `i8::MAX + 1`), so `x <= 128` is a Rust error
/// and the reader must refuse it. The body returns `x`, so if the literal were
/// wrapped to `-128` this would *verify* (`x <= -128` implies `x <= 127`); the
/// honest outcome is a skip.
/// requires: x <= 128
/// ensures: ret <= 127
pub fn contract_out_of_range_literal_is_refused(x: i8) -> i8 {
    x
}

/// The `i8::MIN` boundary shares the bit pattern `0x80` with `128` and must still
/// read: `x >= -128` is true for every `i8`.
/// requires: x >= -128
/// ensures: ret >= -128
pub fn contract_min_bound_still_reads(x: i8) -> i8 {
    x
}

/// `-129` does not fit an `i8` either, so `x >= -129` is refused. Wrapping it to
/// `127` would make `x >= 0` hold for the whole (empty) precondition set, a false
/// proof; the refusal keeps it visible.
/// requires: x >= -129
/// ensures: ret >= 0
pub fn contract_out_of_range_negation_is_refused(x: i8) -> i8 {
    x
}

/// The `i16` case is legal and must still read: `-129` fits an `i16`, so
/// `x >= -129` is a real (non-vacuous) precondition.
/// requires: x >= -129
/// ensures: ret >= -129
pub fn contract_negative_bound_reads_at_i16(x: i16) -> i16 {
    x
}

/// A comparison between two *constants* has no typed name to take its width from,
/// but it still has to be one rustc would accept. `128 <= i8::MAX` is a `literal
/// out of range for i8` error, and reading `128` as the bit pattern `0x80` made it
/// `-128 <= 127` -- always true -- so the shape is refused, not decided.
/// requires: 128 <= i8::MAX && x == 7
/// ensures: ret == 0
pub fn contract_constant_vs_constant_out_of_range(x: i8) -> i8 {
    x
}

/// The in-range counterpart, so the refusal above is pinned to the value and not
/// to the shape: `127 <= i8::MAX` is well-typed and must read.
/// requires: 127 <= i8::MAX && x == 7
/// ensures: ret == 7
pub fn contract_constant_vs_constant_in_range(x: i8) -> i8 {
    x
}

/// A constant *arithmetic* expression that overflows its operand width is a rustc
/// const-eval error (`200u8 + 100u8`), so it must be refused rather than folded
/// mod 256. Folding made `x <= 200 + 100` read as `x <= 44` -- a *stronger*
/// precondition than the author wrote (`x <= 300`, which admits every `u8`), and
/// `ensures: ret <= 44` was then proved for a body that fails at `x == 100`: a
/// false proof.
/// requires: x <= 200 + 100
/// ensures: ret <= 44
pub fn contract_constant_sum_overflow_is_refused(x: u8) -> u8 {
    x
}

/// An unsigned constant expression that goes negative is a rustc error too
/// (`0u8 - 1u8`), and the reader refuses it rather than wrapping to `255`.
/// requires: x >= 0 - 1
/// ensures: ret >= 0
pub fn contract_constant_underflow_is_refused(x: u8) -> u8 {
    x
}

/// `i8::MIN / -1` and `i8::MIN % -1` overflow the signed operand, which rustc
/// rejects; the engine's divider would wrap them to `MIN` and `0`.
/// requires: true
/// ensures: ret == i8::MIN / -1
pub fn contract_constant_div_overflow_is_refused() -> i8 {
    -128
}

/// The in-range counterpart: a constant sum that *does* fit reads as written, so
/// the refusal above is pinned to the overflow and not to constant arithmetic.
/// requires: x <= 100 + 44
/// ensures: ret <= 144
pub fn contract_constant_sum_in_range_reads(x: u8) -> u8 {
    x
}

/// A constant sum that overflows its *narrow* operand but fits a wider one is
/// legal in rustc (`200 + 100` is `300` for a `u16`), so it must still read.
/// requires: x as u16 <= 200 + 100
/// ensures: ret == x
pub fn contract_constant_sum_wider_operand_reads(x: u8) -> u8 {
    x
}

/// The signed trap: `i8::MAX + 1` is `128`, which fits an *unsigned* byte but not
/// a signed one, and rustc rejects it. Widening the exact result at the
/// expression's own signedness is what refuses it; an unsigned widening left it at
/// eight bits where it read as `-128` -- a false proof of the same kind the fold
/// exists to prevent.
/// requires: x <= i8::MAX + 1
/// ensures: ret <= 0
pub fn contract_constant_signed_sum_overflow_is_refused(x: i8) -> i8 {
    x
}

/// A *signed* constant compared with an *unsigned* operand is refused.
///
/// Rust infers a literal's type from the operand it meets, and `x == -1` for a
/// `u8` does not compile ("cannot apply unary operator `-` to type `u8`"). The
/// reader carries the negation as a bit pattern at the operand's width, so it read
/// `x == -1` as `x == 255` -- a wrong *value*, and `ensures: ret == 255` was
/// *proved* for a body returning `x`, which is a false proof. Refusing the shape is
/// the only sound answer; the wrong reading is a proof, so it cannot be a warning.
/// requires: x == -1
/// ensures: ret == 255
pub fn contract_signed_literal_vs_unsigned_is_refused(x: u8) -> u8 {
    x
}

/// The legal counterpart: a bare literal is unsigned, so `0xFF` against a `u8`
/// must still read as `255`. Refusing every literal would be as wrong as refusing
/// none, and this is the case that keeps the check from being a blanket ban.
/// requires: x <= 0xFF
/// ensures: ret == x
pub fn contract_unsigned_literal_still_reads(x: u8) -> u8 {
    x
}

/// The same mixed-sign shape at the *arithmetic* level, where it is equally a
/// rustc error and equally a false proof if read. `x + -1 >= 0` for a `u8` is
/// trivially true when the negation is read as `255`, so this postcondition was
/// *proved* for a body returning `x` -- a false proof the comparison-level check
/// alone did not close.
/// requires: x + -1 >= 0
/// ensures: ret != 0
pub fn contract_signed_constant_sum_vs_unsigned_is_refused(x: u8) -> u8 {
    x
}

/// The legal counterpart at the arithmetic level: an *unsigned* constant still
/// adds and reads, so the refusal is not a blanket ban on constants in sums.
/// requires: x + 255 >= 0
/// ensures: ret == x
pub fn contract_unsigned_constant_sum_still_reads(x: u8) -> u8 {
    x
}

/// And at the *bitwise* level, where the same negation is the same rustc error and
/// the same wrong reading: `x ^ -1 <= 255` read as `x ^ 255 <= 255`, always true,
/// so it was *proved* for a body returning `x`.
/// requires: x ^ -1 <= 255
/// ensures: ret != 0
pub fn contract_signed_constant_mask_vs_unsigned_is_refused(x: u8) -> u8 {
    x
}

/// The legal counterpart at the bitwise level: an unsigned mask still reads.
/// requires: x & 255 == x
/// ensures: ret == x
pub fn contract_unsigned_mask_still_reads(x: u8) -> u8 {
    x
}

// ---------------------------------------------------------------------------
// The contract operators that were missing, and the *precedence* they need.
//
// The expression language had `+ - * & | ^` but no `/ % << >>`, so a contract
// that named a shift, a quotient or a remainder was unreadable -- a dropped
// obligation. The SMT layer already had every one of them (`shl`, `lshr`,
// `ashr`, `udiv`, `urem`, `sdiv`, `srem`) and the body used them; only the
// parser never reached them.
//
// Adding the shifts exposed a second, quieter problem: the reader had just two
// levels and put `|`/`^` beside `+`/`-` and `&` beside `*`, which is *not*
// Rust's order. `x & 1 + 1` was read as `(x & 1) + 1` where Rust means
// `x & (1 + 1)` -- a different number, so a contract could pass or fail against
// the wrong value. That was latent only because no contract mixed the levels;
// the ladder below is now Rust's own, `| ^ & << >> + - * / %` from loosest to
// tightest.

/// A logical right shift of an unsigned value: `x >> 1` is `x / 2`.
/// requires: true
/// ensures: ret == x >> 1
pub fn contract_shr_unsigned(x: u8) -> u8 {
    x >> 1
}

/// The tripwire: `>>` is a value, not a free variable, so naming it one too high
/// is false for every input.
/// requires: true
/// ensures: ret == (x >> 1) + 1
pub fn contract_shr_unsigned_tripwire(x: u8) -> u8 {
    x >> 1
}

/// A left shift: `x << 2` is `x * 4` for the values that do not overflow.
/// requires: x <= 63
/// ensures: ret == x << 2
pub fn contract_shl(x: u8) -> u8 {
    x << 2
}

/// A *signed* right shift is arithmetic, not logical: `-8 >> 1` is `-4`, where a
/// logical shift would give a large positive. This is the entry that separates
/// the two, and the reason the parser reads the left operand's sign.
/// requires: x == -8
/// ensures: ret == -4
pub fn contract_shr_signed_is_arithmetic(x: i8) -> i8 {
    x >> 1
}

/// The tripwire: `-8 >> 1` is never `-1`, so a logical reading (which would give
/// a large positive) or a wrong amount cannot make this true.
/// requires: x == -8
/// ensures: ret == -1
pub fn contract_shr_signed_is_arithmetic_tripwire(x: i8) -> i8 {
    x >> 1
}

/// An unsigned quotient: `x / 3`.
/// requires: true
/// ensures: ret == x / 3
pub fn contract_udiv(x: u32) -> u32 {
    x / 3
}

/// An unsigned remainder: `x % 10`.
/// requires: true
/// ensures: ret == x % 10
pub fn contract_urem(x: u32) -> u32 {
    x % 10
}

/// The tripwire for division: the quotient is not the dividend, so `ret == x`
/// is false whenever `x >= 3`.
/// requires: true
/// ensures: ret == x
pub fn contract_udiv_tripwire(x: u32) -> u32 {
    x / 3
}

/// A *signed* division must use the signed engine: `-7 / 2` is `-3`, where the
/// unsigned one would give a huge positive. The witness is `-7` and the true
/// value `-3`, so a wrong engine is caught.
/// requires: x == -7
/// ensures: ret == -3
pub fn contract_sdiv(x: i32) -> i32 {
    x / 2
}

/// A signed remainder: `-7 % 2` is `-1` in Rust (the sign follows the dividend).
/// requires: x == -7
/// ensures: ret == -1
pub fn contract_srem(x: i32) -> i32 {
    x % 2
}

/// The tripwire for signed division: `-7 / 2` is never `3` (the truncation is
/// toward zero, so the sign is negative).
/// requires: x == -7
/// ensures: ret == 3
pub fn contract_sdiv_tripwire(x: i32) -> i32 {
    x / 2
}

/// A *constant* signed expression, with no symbolic operand at all. The existing
/// `contract_srem`/`contract_sdiv` entries pin a symbolic argument (`x == -7`),
/// and signedness is read from the names in an expression — so they never
/// exercised the one shape where there is no name to read it from. Here the body
/// is folded by rustc to `-1`, and the contract is the literal `-7 % 3`. Rust says
/// `-1` (the sign follows the dividend); the unsigned engine would say
/// `4294967289 % 3`, i.e. `0`, and refute this.
/// requires: true
/// ensures: ret == -7 % 3
pub fn contract_const_srem_negative() -> i32 {
    -7i32 % 3i32
}

/// The companion for division: `-7 / 2` is `-3`, truncated toward zero. The
/// unsigned engine would give `2147483641`, a huge positive.
/// requires: true
/// ensures: ret == -7 / 2
pub fn contract_const_sdiv_negative() -> i32 {
    -7i32 / 2i32
}

/// The companion for an arithmetic shift: `-8 >> 1` is `-4` on a signed operand.
/// A logical reading would give `2147483644`.
/// requires: true
/// ensures: ret == -8 >> 1
pub fn contract_const_ashr_negative() -> i32 {
    -8i32 >> 1
}

/// The tripwire: `-7 % 3` is `-1`, never `2` (which is what a remainder that
/// followed the *divisor's* sign would give). The body is `-1`, so `2` is
/// refuted.
/// requires: true
/// ensures: ret == 2
pub fn contract_const_srem_negative_tripwire() -> i32 {
    -7i32 % 3i32
}

/// The tripwire for the shift: `-8 >> 1` is `-4`, never `-1`.
/// requires: true
/// ensures: ret == -1
pub fn contract_const_ashr_negative_tripwire() -> i32 {
    -8i32 >> 1
}

/// The same unsigned flag decides a *comparison*, not only `/ % >>`. `-7 < 3` is
/// true on a signed reading and false on an unsigned one (`4294967289 < 3`), so a
/// literal that reports itself unsigned made this precondition unsatisfiable —
/// the safe direction, but wrong. The body returns `1`, so the postcondition is
/// true whenever the precondition is.
/// requires: -7 < 3
/// ensures: ret == 1
pub fn contract_const_cmp_negative() -> u8 {
    1
}

/// The tripwire: `-7 > 0` is false, so a *signed* reading makes the precondition
/// unsatisfiable and the function vacuous. An unsigned reading (`4294967289 > 0`)
/// would make it true and the function verify — so a regression here shows up as
/// this entry *passing*, which is the direction to watch.
/// requires: -7 > 0
/// ensures: ret == 1
pub fn contract_const_cmp_negative_tripwire() -> u8 {
    1
}

/// Precedence: Rust reads `x & 1 + 1` as `x & (1 + 1)`, i.e. `x & 2`. The body
/// computes `x & 2`, so a parser that read `(x & 1) + 1` would refute this.
/// requires: true
/// ensures: ret == x & 1 + 1
pub fn contract_precedence_and_over_add(x: u8) -> u8 {
    x & 2
}

/// The tripwire that separates the two readings. At `x == 1`, `1 & 2` is `0`
/// while `(1 & 1) + 1` is `2`; the body computes `0`, so the `2` reading is
/// refuted with witness `x == 1`.
/// requires: x == 1
/// ensures: ret == 2
pub fn contract_precedence_and_over_add_tripwire(x: u8) -> u8 {
    x & 2
}

/// Precedence between `+` and `<<`: `x + 1 << 1` is `(x + 1) << 1` in Rust,
/// because `+` binds tighter than `<<`. The body computes `(x + 1) << 1`. The
/// bound keeps both the `x + 1` and the `<< 1` in range, so the body does not
/// panic -- an unbounded `u8` would make the function *panic* rather than verify,
/// which is a true result but not the one this entry is about.
/// requires: x <= 126
/// ensures: ret == x + 1 << 1
pub fn contract_precedence_add_over_shl(x: u8) -> u8 {
    (x + 1) << 1
}

/// The tripwire: `(x + 1) << 1` is `2x + 2`, never `2x + 1`, so a reading that
/// shifted the wrong side is refuted.
/// requires: x <= 126
/// ensures: ret == x * 2 + 1
pub fn contract_precedence_add_over_shl_tripwire(x: u8) -> u8 {
    (x + 1) << 1
}

/// Precedence between `&` and `|`: `x & 3 | 4` is `(x & 3) | 4`, because `&` binds
/// tighter. The two readings differ at `x == 0`, where the correct one is `4` and
/// `x & (3 | 4)` is `0`. The body computes the correct `4`.
/// requires: x == 0
/// ensures: ret == x & 3 | 4
pub fn contract_precedence_and_over_or(x: u8) -> u8 {
    (x & 3) | 4
}

/// The tripwire: at `x == 0` the `|`-binds-first reading gives `0`, which the body
/// does not, so it is refuted -- unless the parser took that reading, in which case
/// this would verify.
/// requires: x == 0
/// ensures: ret == 0
pub fn contract_precedence_and_over_or_tripwire(x: u8) -> u8 {
    (x & 3) | 4
}

/// Precedence between a shift and a comparison: `x >> 1 == 2` is `(x >> 1) == 2`,
/// because `<<`/`>>` bind tighter than `==`. The body returns `1` iff the comparison
/// holds, so the contract is the comparison itself at a pinned point.
/// requires: x == 4
/// ensures: x >> 1 == 2
pub fn contract_precedence_shift_over_eq(x: u8) -> u8 {
    0
}

/// The false direction of the same shape: `x >> 1 == 2` at `x == 8` is `4 == 2`,
/// which is false, so the body returning `1` is refuted. Together with the entry
/// above this pins that the comparison is *decided*, not merely read: a reader that
/// dropped the shift and compared `x == 2` would also refute here, but a reader that
/// read the shift as `x >> (1 == 2)` = `x >> 0` = `x` and then proved the equality
/// would have proved a false thing. The verifying entry is the one that separates
/// those, because only the correct reading is true there.
/// requires: x == 8
/// ensures: x >> 1 == 2
pub fn contract_precedence_shift_over_eq_tripwire(x: u8) -> u8 {
    1
}

/// Precedence between a cast and `+`: `x as i16 + 1` is `(x as i16) + 1`, because a
/// cast binds tighter than arithmetic. The body computes `(x as i16) + 1`.
/// requires: x == 5
/// ensures: ret == x as i16 + 1
pub fn contract_precedence_cast_over_add(x: i8) -> i16 {
    x as i16 + 1
}

/// Precedence between unary `-` and a cast: `-x as i16` is `(-x) as i16`, because
/// unary operators bind tighter than `as`. The body computes `(-x) as i16`.
/// requires: x == 1
/// ensures: ret == -x as i16
pub fn contract_precedence_neg_over_cast(x: i8) -> i16 {
    -x as i16
}

/// Precedence between unary `-` and `%`, and the *sign* of a remainder: `-x % 2` is
/// `(-x) % 2`, and Rust truncates toward zero, so at `x == 3` it is `-1`. The body
/// computes `-3 % 2`.
/// requires: x == 3
/// ensures: ret == -x % 2
pub fn contract_precedence_neg_over_rem(x: i8) -> i8 {
    -3 % 2
}

/// Left associativity at equal precedence: `2 * 3 % 4` is `(2 * 3) % 4`, i.e. `2`,
/// not `2 * (3 % 4)` which is `6`. A constant, so there is no input to vary.
/// requires: true
/// ensures: ret == 2 * 3 % 4
pub fn contract_precedence_mul_rem_left_assoc() -> u8 {
    2
}

// ---------------------------------------------------------------------------
// 128-bit types: wider than the engine, and refused as a whole function.
//
// The engine's words are 1..=64 bits, and every width-taking constructor
// (`smt::var`, `truncate`, …) asserts that. A `u128`/`i128` argument, local,
// return or *cast target* therefore has no width to model, and the function is
// refused rather than half-modelled. The refusal is a `Skipped`, not a panic:
// the guard runs before the argument seeding, the loop havoc and the contract
// bindings, any of which would otherwise assert in whichever ran first and take
// the whole run down with it. These entries pin that the *tool survives* a
// 128-bit function and reports it, which is the property a crash would break.

/// A `u128` argument: refused, not panicked.
/// requires: true
/// ensures: ret == x
pub fn wide_arg(x: u128) -> u128 {
    x
}

/// A `u128` return with an ordinary argument: refused on the return type alone.
/// requires: true
/// ensures: true
pub fn wide_return(x: u8) -> u128 {
    x as u128
}

/// A `u128` *local* inside a loop: the loop havoc consults the type's width, so
/// this is the path that would panic without the guard.
/// requires: true
/// invariant: x == 0
/// ensures: ret == 0
pub fn wide_local_in_loop() -> u8 {
    let mut x: u128 = 0;
    let mut i = 0u8;
    while i < 3 {
        x = x + 1;
        i += 1;
    }
    0
}

/// A contract casting to `u128`, with no 128-bit local at all: the refusal has to
/// come from the *parser*, since the function's own types are all 64-bit.
/// requires: true
/// ensures: ret == x as u128
pub fn wide_cast_in_contract(x: u8) -> u64 {
    x as u64
}

/// A `u64` function next to the 128-bit ones, to show the guard does not spill:
/// this one still verifies.
/// requires: true
/// ensures: ret == x as u64
pub fn narrow_64_still_works(x: u8) -> u64 {
    x as u64
}

// ---------------------------------------------------------------------------
// `count_ones` and `wrapping_abs`: the two `core::num` methods that are neither
// a two-operand family nor an `Option`. `count_ones` widens its result (`u8` ->
// `u32`), which is the one place a modelled call's result width differs from its
// operand's; `wrapping_abs` is unary and reads its operand's sign.
//
// Each pair below is one *verified* contract and one *tripwire*, per the
// standing rule: a shape is not supported until a corpus entry verifies **and**
// one fails, because a shape that only ever verifies is one whose model has
// never been contradicted.
// ---------------------------------------------------------------------------

/// A zero operand has no set bits and every other value has at least one, so the
/// count is at least 1. This is the shape `checked_*` cannot express: the result
/// type is `u32` while the operand is `u8`.
/// requires: x != 0
/// ensures: ret >= 1
pub fn popcount_of_nonzero(x: u8) -> u32 {
    x.count_ones()
}

/// The tripwire: a `u8` has eight bits, so the count is at least 2 for every
/// nonzero operand -- which is false at `x == 1`, whose count is 1.
/// requires: x != 0
/// ensures: ret >= 2
pub fn popcount_of_nonzero_tripwire(x: u8) -> u32 {
    x.count_ones()
}

/// The count cannot exceed the operand's width. Stated at the top of the range,
/// where the *widened* result would be wrong if the model left it 8-bit.
/// ensures: ret <= 8
pub fn popcount_bounded_by_width(x: u8) -> u32 {
    x.count_ones()
}

/// The tripwire: `x == 0xFF` has eight set bits, so a bound of 7 is false.
/// ensures: ret <= 7
pub fn popcount_bounded_by_width_tripwire(x: u8) -> u32 {
    x.count_ones()
}

/// `wrapping_abs` never returns a value below its operand: it is the identity on
/// non-negative inputs and the negation on negative ones, and at `MIN` it wraps
/// back to `MIN` itself. All three cases are `ret >= x`, which is why this is
/// true including at the `MIN` point where the magnitude is unrepresentable.
/// ensures: ret >= x
pub fn abs_never_below_operand(x: i8) -> i8 {
    x.wrapping_abs()
}

/// The tripwire: strict inequality fails at `x == 0`, where `abs` is the identity
/// and the result equals the operand.
/// ensures: ret > x
pub fn abs_never_below_operand_tripwire(x: i8) -> i8 {
    x.wrapping_abs()
}

// ---------------------------------------------------------------------------
// The rest of the unary `core::num` surface.
//
// `leading_zeros` and `trailing_zeros` sit beside `count_ones`, and the four
// families each define `neg` and (on the signed types) `abs`. These are the
// shapes where the *type* decides what a method means: `wrapping_neg` on a `u8`
// is modular, `saturating_neg` does not exist on a `u8` at all, and `MIN` is the
// one input where `neg` and `abs` have no representable result. Each pair below
// is one verifying contract and one tripwire.
// ---------------------------------------------------------------------------

/// `leading_zeros` counts the zero bits above the highest set bit, so an operand
/// below `0x80` has at least one -- and the count is on the widened `u32` result.
/// requires: x < 128
/// ensures: ret >= 1
pub fn leading_zeros_of_a_small_value(x: u8) -> u32 {
    x.leading_zeros()
}

/// The tripwire: `x == 0` has eight leading zeros, so a bound of *nine* is false
/// even though it looks safe for every non-zero operand.
/// requires: x < 128
/// ensures: ret >= 9
pub fn leading_zeros_of_a_small_value_tripwire(x: u8) -> u32 {
    x.leading_zeros()
}

/// `trailing_zeros` counts the zero bits below the lowest set bit, so a value
/// with the top bit set has at most seven of them.
/// requires: x >= 128
/// ensures: ret <= 7
pub fn trailing_zeros_of_a_top_bit_value(x: u8) -> u32 {
    x.trailing_zeros()
}

/// The tripwire: `x == 0x80` has exactly seven trailing zeros, so a bound of six
/// is false -- and the witness is the smallest operand the precondition allows.
/// requires: x >= 128
/// ensures: ret <= 6
pub fn trailing_zeros_of_a_top_bit_value_tripwire(x: u8) -> u32 {
    x.trailing_zeros()
}

/// `saturating_neg` of a positive value is negative: the negation is in range, so
/// no clamp happens, and the result is `-x`.
/// requires: x > 0
/// ensures: ret < 0
pub fn saturating_neg_of_positive_is_negative(x: i8) -> i8 {
    x.saturating_neg()
}

/// The tripwire: the *wrapping* negation of `x == 0` is `0`, which is not
/// negative, so the same claim without the positivity precondition is false.
/// requires: true
/// ensures: ret < 0
pub fn wrapping_neg_is_negative_tripwire(x: i8) -> i8 {
    x.wrapping_neg()
}

/// `saturating_abs` is the magnitude, and at `MIN` -- where the magnitude is not
/// representable -- it clamps to `MAX` rather than wrapping back to `MIN`. So the
/// result is never negative, for any operand.
/// requires: true
/// ensures: ret >= 0
pub fn saturating_abs_is_never_negative(x: i8) -> i8 {
    x.saturating_abs()
}

/// The tripwire: the *wrapping* absolute value of `MIN` is `MIN`, which is
/// negative, so the same claim about the wrapping family is false.
/// requires: true
/// ensures: ret >= 0
pub fn wrapping_abs_is_never_negative_tripwire(x: i8) -> i8 {
    x.wrapping_abs()
}

/// `saturating_neg` of a non-positive value clamps to zero rather than wrapping,
/// which is what distinguishes it from `wrapping_neg` at `MIN`.
/// requires: x <= 0
/// ensures: ret >= 0
pub fn saturating_neg_of_non_positive_is_non_negative(x: i8) -> i8 {
    x.saturating_neg()
}

/// The tripwire: `wrapping_neg` at `MIN` is `MIN`, which is negative.
/// requires: x <= 0
/// ensures: ret >= 0
pub fn wrapping_neg_of_non_positive_is_non_negative_tripwire(x: i8) -> i8 {
    x.wrapping_neg()
}

/// `saturating_abs` is monotone in the sense that its result is at least the
/// operand when the operand is non-negative -- where it is the identity.
/// requires: x >= 0
/// ensures: ret == x
pub fn saturating_abs_of_non_negative_is_identity(x: i8) -> i8 {
    x.saturating_abs()
}

/// The tripwire: for a *negative* operand the identity claim fails, and the
/// witness is the negation.
/// requires: true
/// ensures: ret == x
pub fn saturating_abs_is_identity_tripwire(x: i8) -> i8 {
    x.saturating_abs()
}

// ---------------------------------------------------------------------------
// The two-operand `overflowing_*` family, read through a `ret.N` contract.
//
// This is the family whose result is a `(T, bool)` tuple: the wrapped value in
// field 0 and the overflow flag in field 1. A modelled call writes those two
// fields directly, without ever assigning the tuple local as a whole, so a
// postcondition naming `ret.1` reaches a component that lives in the *field*
// store rather than the element store. Until the return-component reader
// consulted both, `ret.1` came back unbound and the whole contract was refused
// as an aggregate with no such component -- a refusal that looked like a
// modelling gap but was a store mismatch.
//
// As always, each shape carries one verifying contract and one tripwire.
// ---------------------------------------------------------------------------

/// The flag is set exactly when the addition overflowed, so either it did
/// (the flag is `true`) or the wrapped value is the exact sum. This is the whole
/// meaning of `overflowing_add` in one contract, and it reads *both* components
/// of the return through `ret.0` and `ret.1`.
/// requires: true
/// ensures: ret.1 == true || ret.0 == x + y
pub fn overflowing_add_flag_or_exact_sum(x: u8, y: u8) -> (u8, bool) {
    x.overflowing_add(y)
}

/// The tripwire: the flag is *not* always clear -- `0xFF + 1` overflows -- so a
/// contract that reads `ret.1` and claims it is false must fail.
/// requires: true
/// ensures: ret.1 == false
pub fn overflowing_add_flag_never_set_tripwire(x: u8, y: u8) -> (u8, bool) {
    x.overflowing_add(y)
}

/// A guarded addition: with `x < 16` and `y < 16` the sum fits in a `u8`, so the
/// flag is clear -- and this reads the flag, not just the value.
/// requires: x < 16
/// requires: y < 16
/// ensures: ret.1 == false
pub fn overflowing_add_small_operands_never_flag(x: u8, y: u8) -> (u8, bool) {
    x.overflowing_add(y)
}

/// The tripwire: dropping the second bound lets `y == 0xFF` through, and
/// `16 + 0xFF` overflows, so the flag is not always clear.
/// requires: x < 16
/// ensures: ret.1 == false
pub fn overflowing_add_one_bound_only_tripwire(x: u8, y: u8) -> (u8, bool) {
    x.overflowing_add(y)
}

/// When the addition does not overflow the wrapped value *is* the sum, so a
/// contract on `ret.0` alone is checkable and must agree with the body's own
/// arithmetic. The precondition is what makes it true, and it is the value
/// component this time rather than the flag.
/// requires: x < 16
/// requires: y < 16
/// ensures: ret.0 == x + y
pub fn overflowing_add_value_is_exact_when_no_overflow(x: u8, y: u8) -> (u8, bool) {
    x.overflowing_add(y)
}

/// The tripwire: the wrapped value is *not* always at least the left operand.
/// The contract's own `+` wraps at `u8` exactly as the method does, so an
/// "exact sum" claim cannot distinguish the two -- the place the wrapping shows
/// is the order. `0xFF + 1` wraps to `0`, below `x`, and the witness finds it.
/// requires: true
/// ensures: ret.0 >= x
pub fn overflowing_add_wrapped_value_below_operand_tripwire(x: u8, y: u8) -> (u8, bool) {
    x.overflowing_add(y)
}


// ---------------------------------------------------------------------------
// The `pow` families, read through a `u32` exponent beside a base of the
// method's own width.
//
// `pow` is the first modelled call with two operands of *different* types: the
// base has the method's width and sign, and the exponent is the `u32` it is
// declared as. The frontend reads the exponent on its own, from the argument's
// type, rather than as a second operand at the base's width -- reading it at the
// base's width would fold the wrong number of bits.
//
// All four families are modelled because `pow`'s failure is an *overflow*, and an
// overflow is a value in every family: `wrapping_pow` wraps, `saturating_pow`
// clamps, `checked_pow` returns `None` and `overflowing_pow` sets the flag. The
// plain `pow`, which panics on overflow, is not modelled at all -- hiding that
// panic is not something a proof may do.
//
// Each shape carries one verifying contract and one tripwire, per the standing
// rule.
// ---------------------------------------------------------------------------

/// `wrapping_pow(2, 7)` is `128`, which fits in a `u8`; the same base at exponent
/// `8` wraps to `0`. Stated on the wrapped value, where a wrong fold shows as a
/// wrong number.
/// requires: true
/// ensures: ret == 128
pub fn wrapping_pow_two_to_seven_is_128() -> u8 {
    2u8.wrapping_pow(7)
}

/// The tripwire: `2^8` wraps to `0` at a `u8`. `256` cannot be written here --
/// the frontend refuses a literal that does not fit the operand's width, which is
/// the right refusal, so the claim names the *neighbouring* value instead: a
/// model that stopped one step early, or folded at the wrong width and truncated
/// only at the end, agrees on `2^7 == 128` and fails here.
/// requires: true
/// ensures: ret == 128
pub fn wrapping_pow_two_to_eight_is_256_tripwire() -> u8 {
    2u8.wrapping_pow(8)
}

/// `checked_pow` returns `None` exactly where `wrapping_pow` overflowed, so the
/// match arms meet the `Some` case at `2^7`.
/// requires: true
/// ensures: ret == 128
pub fn checked_pow_two_to_seven_is_some_128() -> u8 {
    match 2u8.checked_pow(7) {
        Some(v) => v,
        None => 0,
    }
}

/// The tripwire: `checked_pow(2, 8)` is `None`, so the `None` arm runs and the
/// result is `0`, not `255`.
/// requires: true
/// ensures: ret == 255
pub fn checked_pow_two_to_eight_is_none_tripwire() -> u8 {
    match 2u8.checked_pow(8) {
        Some(v) => v,
        None => 0,
    }
}

/// `saturating_pow(3, 5)` is `243`, in range, so no clamp happens.
/// requires: true
/// ensures: ret == 243
pub fn saturating_pow_three_to_five_is_243() -> u8 {
    3u8.saturating_pow(5)
}

/// The tripwire: `3^6` is `729`, past `u8::MAX`, so `saturating_pow` clamps to
/// `255` rather than wrapping to `217`.
/// requires: true
/// ensures: ret == 217
pub fn saturating_pow_three_to_six_clamps_tripwire() -> u8 {
    3u8.saturating_pow(6)
}

/// The overflow flag is set exactly where the product overflowed, so either it
/// fired or the value is the exact power -- and `2^7` does not overflow.
/// requires: true
/// ensures: ret.1 == false
pub fn overflowing_pow_two_to_seven_did_not_overflow() -> (u8, bool) {
    2u8.overflowing_pow(7)
}

/// The tripwire: `2^8` *does* overflow a `u8`, so the flag is `true` and the
/// claim that it did not is false.
/// requires: true
/// ensures: ret.1 == false
pub fn overflowing_pow_two_to_eight_flag_tripwire() -> (u8, bool) {
    2u8.overflowing_pow(8)
}

/// A signed base: `(-2)^7` is `-128`, the one value in range at this magnitude,
/// so the wrap does not happen and the result is exactly `MIN`.
/// requires: true
/// ensures: ret == -128
pub fn wrapping_pow_negative_two_to_seven_is_min() -> i8 {
    (-2i8).wrapping_pow(7)
}

/// The tripwire: `(-2)^8` is `256`, past `i8::MAX`, and wraps to `0`. The true
/// value is not writable as an `i8` literal, so the claim names `i8::MAX`: a
/// model that read the exponent's bits as signed, or that clamped the signed case
/// to `MAX` instead of wrapping it, lands there and refutes the claim.
/// requires: true
/// ensures: ret == 127
pub fn wrapping_pow_negative_two_to_eight_wraps_tripwire() -> i8 {
    (-2i8).wrapping_pow(8)
}

/// `saturating_pow` of a negative base with an *odd* exponent is negative and
/// past the range, so it clamps to `MIN` rather than `MAX`. This is the signed
/// clamp direction, and it is the one a "clamp everything to `MAX`" model gets
/// wrong.
/// requires: true
/// ensures: ret == -128
pub fn saturating_pow_negative_base_clamps_to_min() -> i8 {
    (-3i8).saturating_pow(5)
}

/// The tripwire: the same claim pinned to `MAX` is false, because the true result
/// is negative.
/// requires: true
/// ensures: ret == 127
pub fn saturating_pow_negative_base_to_max_tripwire() -> i8 {
    (-3i8).saturating_pow(5)
}

/// `pow(x, 0)` is `1` for every base, including `0`. This is the fold's base
/// case, and it is the one exponent every family agrees on.
/// requires: true
/// ensures: ret == 1
pub fn wrapping_pow_zero_exponent_is_one(x: u8) -> u8 {
    x.wrapping_pow(0)
}

/// The tripwire: `pow(x, 1)` is `x`, not `1`, for every base -- so the claim is
/// false at every base other than `1`.
/// requires: true
/// ensures: ret == 1
pub fn wrapping_pow_one_exponent_is_one_tripwire(x: u8) -> u8 {
    x.wrapping_pow(1)
}


// ---------------------------------------------------------------------------
// The bitwise complement, `!x`.
//
// `!x` is `all_ones ^ x` at the *operand's* width, and the model reads that
// width off the value rather than trusting the destination local's declared
// width -- the two agree for well-typed MIR, and where they would disagree the
// read is refused rather than masked at a width the value does not have.
//
// The shape had no corpus entry before this: `!x` is common in real Rust and was
// modelled, but nothing pinned it, which is exactly the "supported until
// contradicted" gap the standing tripwire rule exists to close.
// ---------------------------------------------------------------------------

/// The complement of zero is all ones: `255` at a `u8`. Stated on the operand's
/// width, so a model that masked at the destination's width would agree here and
/// disagree at a narrower operand.
/// requires: x == 0
/// ensures: ret == 255
pub fn not_of_zero_is_all_ones(x: u8) -> u8 {
    !x
}

/// `!x == 255 - x` at a `u8`, the identity the mask at the operand's width gives.
/// An operand is named so the claim is symbolic rather than one input.
/// requires: true
/// ensures: ret == 255 - x
pub fn not_is_255_minus_x(x: u8) -> u8 {
    !x
}

/// The tripwire: `!x` is `255` only at `x == 0`, so claiming it always is false
/// at every other input. A model that ignored the operand -- `all_ones ^ 0`, or a
/// constant `255` -- would prove this.
/// requires: true
/// ensures: ret == 255
pub fn not_is_always_255_tripwire(x: u8) -> u8 {
    !x
}

/// The complement keeps the operand's sign, so at an `i8` the complement of zero
/// is `-1`, not `255` -- the same bit pattern read as the operand's type.
/// requires: x == 0
/// ensures: ret == -1
pub fn not_of_zero_is_minus_one(x: i8) -> i8 {
    !x
}

/// The width is the operand's, so a `u32` complement of zero is `4294967295`
/// rather than the `u8` value. This is the width the mask must be derived from.
/// requires: x == 0
/// ensures: ret == 4294967295
pub fn not_of_zero_u32_is_all_ones(x: u32) -> u32 {
    !x
}

// ---------------------------------------------------------------------------
// A contract written above a struct belongs to the struct, not the next function.
//
// The reader matched a `struct`/`enum` head and `continue`d *without* clearing the
// pending contract, so a doc comment above a layout carried over to the next `fn`.
// A leaked `requires` is a false proof when it is satisfiable: the postcondition is
// only checked for the inputs the precondition admits.
//
// `leaked_requires_tripwire` carries the shape and must be refuted, not verified.
// `leaked_requires_is_dropped` is the same function with the struct removed -- the
// two must agree, which is what makes the tripwire evidence rather than a reading
// of one file.
/// requires: x == 0
pub struct LeakSource {
    pub v: u8,
}

/// The tripwire: `x` is arbitrary, so `ret == 0` is false at `x != 0`. If the
/// struct's `requires: x == 0` leaked in, the check would be made only at `x == 0`
/// and this would *verify* -- the false proof.
/// ensures: ret == 0
pub fn leaked_requires_tripwire(x: u8) -> u8 {
    x
}

/// The control: the identical function and contract with no struct above it. It
/// must be refuted for the same reason, so the tripwire's refutation is the
/// reader dropping the leak and not some other reading.
/// ensures: ret == 0
pub fn leaked_requires_is_dropped(x: u8) -> u8 {
    x
}

// ---------------------------------------------------------------------------
// Two names of different signedness are refused, because rustc refuses them.
//
// `a > b` for an `i8` and a `u8` is `E0308: mismatched types`. The reader used to
// read it as signed; the body reads each operand at its own signedness, so the two
// could disagree. Refusing keeps "the tool could not run" distinct from a verdict.
//
// These are `skipped`, not `verified` and not `failed`: a program rustc rejects
// gets no verdict.
/// requires: a > b
/// ensures: ret != 0
pub fn contract_mixed_signedness_compare_is_refused(a: i8, b: u8) -> u8 {
    b
}

/// The same at an arithmetic level, where the reader also picks a sign.
/// requires: a + b == 0
/// ensures: ret != 0
pub fn contract_mixed_signedness_add_is_refused(a: i8, b: u8) -> u8 {
    b
}

/// The legal counterpart: two names of the *same* signedness compare and read, so
/// the refusal is not a blanket ban on two-name comparisons.
/// requires: a < b
/// ensures: ret == a
pub fn contract_same_signedness_compare_still_reads(a: i8, b: i8) -> i8 {
    a
}

// ---------------------------------------------------------------------------
// A shift of an *untyped* constant is refused, because its width is inferred.
//
// `255 >> 8` looks fine at the scope's width (32, from a `u32` name in scope),
// but the operand has no type of its own: Rust infers its width from where the
// shift is read, and against a `u8` partner `255` is a `u8` and a shift by its own
// width is a compile error. The reader verified `255 >> 8 <= x` for a `u8` `x`, a
// false proof on a program rustc rejects. The amount must be below the narrowest
// width, and a literal operand must fit an 8-bit signed value, or the shift is
// refused -- a skipped function, not a wrong verdict.
//
// These are `skipped`, not `verified` and not `failed`.
/// requires: true
/// ensures: (255 >> 8) <= x
pub fn contract_untyped_shift_amount_over_narrow_width_is_refused(x: u8) -> u8 {
    x
}

/// The left-shift form, and an amount over the narrowest width again.
/// requires: true
/// ensures: (!0 << 8) <= x
pub fn contract_untyped_left_shift_amount_over_narrow_width_is_refused(x: u8) -> u8 {
    x
}

/// The same shape where the operand, not the amount, is what the narrow partner
/// rejects: `255` is a rustc `literal out of range` for an `i8`.
/// requires: true
/// ensures: (255 >> 1) >= y
pub fn contract_untyped_shift_operand_out_of_narrow_range_is_refused(y: i8) -> i8 {
    y
}

/// The control: a shift whose amount is below the narrowest width and whose
/// operand fits an 8-bit signed value is valid at every width, so it reads.
/// requires: x == 32
/// ensures: (1 << 4) <= x
pub fn contract_fitting_untyped_shift_still_reads(x: u8) -> u8 {
    x
}

/// The control: a shift of a *typed* name has a known width, so a larger amount is
/// fine as long as it is below that width.
/// requires: a == 8
/// ensures: (a >> 3) == 1
pub fn contract_typed_shift_still_reads(a: u16) -> u16 {
    a
}

// ---------------------------------------------------------------------------
// A shift *amount* is a value of its own type, not of the shifted operand's.
//
// Rust leaves the amount's type unconstrained, so an unsuffixed amount defaults
// to `i32` and is folded at 32 bits. `x >> (2 << 7)` for a `u8` `x` is then an
// amount of `256` -- a shift overflow, and a rustc error. The reader sized the
// amount's literals to the eight-bit *scope*, so `2 << 7` wrapped to `0` and the
// shift read as `x >> 0`; the reader then *decided* `x >> (2 << 7) == 0` -- false
// at `x == 0` -- on a program rustc rejects. Flooring an amount's bare literals
// at 32 bits makes the fold agree with rustc's `i32` evaluation, so the wrapped
// amount never appears and the shift is refused for the amount it really is.
//
// These are `skipped`, not `verified` and not `failed`.
/// requires: true
/// ensures: (x >> (2 << 7)) == 0
pub fn contract_nested_shift_amount_overflow_is_refused(x: u8) -> u8 {
    x
}

/// The same wrapped amount reached through a `+`, so the floor is on the amount
/// expression as a whole and not only on a bare nested shift.
/// requires: true
/// ensures: (x >> ((2 << 7) + 1)) == 0
pub fn contract_nested_shift_amount_sum_overflow_is_refused(x: u8) -> u8 {
    x
}

/// The control: an amount that fits `i32` and is below the operand width reads.
/// requires: true
/// ensures: (x >> (1 + 1)) <= x
pub fn contract_fitting_shift_amount_still_reads(x: u8) -> u8 {
    x
}

// A *typed* operand inside the amount fixes the amount's type, so the amount is
// folded at that width and not at `i32`. `x >> (1u8 + (2 << 7))` for a `u8` `x` is
// a `u8` amount: `2 << 7` is `0u8`, so the amount is `1u8` and rustc accepts the
// shift. Flooring the amount's literals at a flat `i32` built `2 << 7` as `256`
// and *refused* the shift -- a false refusal on a program rustc accepts.
//
// The first is `verified`; the two negative controls after it are `skipped`.
/// requires: true
/// ensures: (x >> (1u8 + (2 << 7))) <= x
pub fn contract_typed_amount_operand_fixes_the_width(x: u8) -> u8 {
    x
}

/// The negative control: the `u8` suffix sits in the *nested* shift's amount, not
/// among the outer amount's operands, so the outer amount stays the `i32`
/// `2 << 7u8` = `256` -- a shift overflow, and a rustc error.
/// requires: true
/// ensures: (x >> (2 << 7u8)) == 0
pub fn contract_nested_amount_suffix_does_not_fix_the_outer_width(x: u8) -> u8 {
    x
}

/// A cast fixes the amount's type and overrides what it casts: `(1u8) as u16` is a
/// `u16`, so `(1u8) as u16 + (2 << 7)` is `257u16` -- a shift overflow.
/// requires: true
/// ensures: (x >> ((1u8) as u16 + (2 << 7))) == 0
pub fn contract_cast_amount_operand_fixes_the_width(x: u8) -> u8 {
    x
}

// ---------------------------------------------------------------------------
// Every literal and every constant `+ - *` intermediate is range-checked against
// the type the expression meets, not only the value the fold produces.
//
// The reader folds a constant expression to a single value and used to
// range-check only that value. Rust checks each literal and each intermediate, so
// `2 & 128` for an `i8` is a `literal out of range` error although the fold's
// value is `0`, and `128 - 63` is rejected although its value `65` fits. The
// reader decided both, on programs rustc rejects -- a wrong *verdict*, not a false
// proof, but a verdict all the same. The envelope of the literals underneath the
// fold is what refuses them.
//
// These are `skipped`, not `verified` and not `failed`.
/// requires: true
/// ensures: y == (200 & 200)
pub fn contract_literal_in_fold_out_of_range_is_refused(y: i8) -> i8 {
    y
}

/// The masking form: the fold's value `0` fits, but the `128` underneath does not.
/// requires: true
/// ensures: y == (2 & 128)
pub fn contract_masked_literal_out_of_range_is_refused(y: i8) -> i8 {
    y
}

/// A sum whose value `200` is out of range for the `i8` it meets.
/// requires: true
/// ensures: y == (100 + 100)
pub fn contract_constant_sum_value_out_of_range_is_refused(y: i8) -> i8 {
    y
}

/// A difference whose value `65` *fits*, but whose `128` literal does not -- the
/// case a value-only check cannot see.
/// requires: true
/// ensures: y == (128 - 63)
pub fn contract_literal_in_difference_out_of_range_is_refused(y: i8) -> i8 {
    y
}

/// The control: the same literals under a `u8` partner fit, so the comparison
/// reads. This keeps the refusal drawn at the range, not at the fold.
/// requires: x == 200
/// ensures: x == (200 & 200)
pub fn contract_fold_literals_in_range_still_read(x: u8) -> u8 {
    x
}

/// The control: `-128` is the one bare literal a unary `-` rescues for an `i8`,
/// because the negated value, not the magnitude, is what meets the type.
/// requires: y == -128
/// ensures: ret == y
pub fn contract_bare_negated_bound_still_reads(y: i8) -> i8 {
    y
}

/// A literal *inside* a fold is not rescued by a surrounding `-`: `-(128 - 63)` is
/// rejected for its inner `128`, unlike `-(128)`.
/// requires: true
/// ensures: y == -(128 - 63)
pub fn contract_literal_in_negated_fold_is_refused(y: i8) -> i8 {
    y
}

/// A shift amount that is an untyped complement has no width of its own: `!254` is
/// `-255` at the `i32` Rust infers (a shift overflow) but `1` at eight bits, so
/// the shape is refused rather than read at the scope's width.
/// requires: true
/// ensures: y < (100 >> (!254))
pub fn contract_complement_shift_amount_is_refused(y: i8) -> i8 {
    y
}

// ---------------------------------------------------------------------------
// A fold that mixes an untyped complement with a plain operand is refused when its
// value depends on the signedness Rust infers for it.
//
// A complement (`!127`) has no signedness of its own -- it takes the one the type
// it meets gives it -- and the reader guesses it from the other operand. When no
// operand fixes a sign the guess can disagree with the reading the fold finally
// gets, and the fold's value, and whether it overflows at all, change with it:
// `!127 - 63` is `128 - 63 = 65` unsigned but `i8::MIN - 63` -- a rustc overflow --
// signed. The reader decided `65` for a program rustc rejects. So the shape is
// refused when the two readings disagree on the overflow.
//
// These are `skipped`, not `verified` and not `failed`.
/// requires: true
/// ensures: y == ((!127) - 63)
pub fn contract_sign_ambiguous_fold_is_refused(y: i8) -> i8 {
    y
}

/// The multiplication form, where the signed reading overflows and the unsigned one
/// does not: `!127 * 2` is `i8::MIN * 2` (a rustc overflow) but `128 * 2 = 256`
/// unsigned.
/// requires: true
/// ensures: y == ((!127) * 2)
pub fn contract_sign_ambiguous_mul_is_refused(y: i8) -> i8 {
    y
}

/// A negated bare literal beside an untyped complement is legal only at a signed
/// type (`!100 * -0` is `E0277` for a `u16`), so the shape is refused rather than
/// decided on the wrong reading.
/// requires: true
/// ensures: a == ((!100) * (-0))
pub fn contract_complement_with_negated_literal_is_refused(a: u16) -> u16 {
    a
}

/// The control: the same fold under a *wider* partner is accepted by rustc and must
/// still be decided. `(!127) - 63` at sixteen bits is `65408 - 63 = 65345`, in
/// range, so the two readings agree and the shape reads.
/// requires: a == 65345
/// ensures: a == ((!127) - 63)
pub fn contract_sign_ambiguous_fold_at_wider_width_reads(a: u16) -> u16 {
    a
}

/// The control: a fold of untyped operands that agrees under both readings still
/// reads. `(!0) - 1` is `255 - 1 = 254` unsigned and `-1 - 1 = -2` signed, and
/// *neither* overflows at eight bits, so the reader may decide it.
/// requires: x == 254
/// ensures: x == ((!0) - 1)
pub fn contract_agreeing_untyped_fold_still_reads(x: u8) -> u8 {
    x
}

// ---------------------------------------------------------------------------
// The written magnitude of a suffixed literal is what Rust range-checks, and a
// complement's operand envelope must not leak onto an unrelated literal that
// shares the complement's value term.
//
// `128i8` alone is a `literal out of range for i8` error and only `-128i8` is
// legal, because the negation is what meets the type. Recording the *signed value*
// (`-128`) instead of the written magnitude made the negation add `+128` to the
// envelope and refuse the valid `-128i8`; it also made the positive `128i8`, which
// rustc rejects, read as the in-range `-128` -- a wrong verdict in both directions.
//
// The complement is worse: at eight bits `!128` is the constant `127`, which the
// engine hash-conses with a separately written bare `127`. Recording the operand
// envelope (`128`) in the global term-keyed map attached it to that innocent `127`,
// so `x == !128 && y == 127` for a `u8` and an `i8` -- both valid Rust -- was
// skipped. The envelope now travels in the operand's own payload.
//
// These first two are `skipped`: the shapes are rustc range errors.
/// requires: true
/// ensures: y == 128i8
pub fn contract_suffixed_positive_min_magnitude_is_refused(y: i8) -> i8 {
    y
}

/// requires: true
/// ensures: y == -(-128i8)
pub fn contract_double_negated_min_is_refused(y: i8) -> i8 {
    y
}

/// The control: `-128i8` is the one suffixed literal a unary `-` rescues, because
/// the negated value, not the magnitude, is what meets the type. It must read.
/// requires: y == -128i8
/// ensures: ret == y
pub fn contract_suffixed_min_literal_still_reads(y: i8) -> i8 {
    y
}

/// The control: a plain positive suffixed literal well inside range reads.
/// requires: b == 128i16
/// ensures: ret == b
pub fn contract_suffixed_positive_literal_still_reads(b: i16) -> i16 {
    b
}

/// The two-conjunct case: `x == !128` is a legal `u8` complement and `y == 127` is
/// a legal `i8` comparison. The complement's operand (`128`) must not be charged to
/// the unrelated `127`, so the whole contract reads.
/// requires: x == !128 && y == 127
/// ensures: ret == 0
pub fn contract_complement_does_not_pollute_a_bare_literal(x: u8, y: i8) -> u8 {
    let _ = (x, y);
    0
}

/// The refusal the complement still owes: `!128` against an `i8` is a `literal out
/// of range for i8` error, because Rust checks the operand `128`.
/// requires: true
/// ensures: y <= (!128)
pub fn contract_complement_operand_out_of_range_is_refused(y: i8) -> i8 {
    y
}

/// The refusal survives a unary `-` around the complement: `-!128` for an `i8` is a
/// rustc error for the same operand `128`, so the envelope must travel through the
/// negation, which is a *value* and cannot carry it in the sign.
/// requires: true
/// ensures: (-(!128)) <= y
pub fn contract_negated_complement_operand_is_refused(y: i8) -> i8 {
    y
}

/// A nested complement whose operand is a *fold*: `!(!1 - 200)` for an `i8` is a
/// rustc error for the `200`, and the reader must keep it. The inner complement
/// `!1` carries `(1, 1)` in its sign, and the fold `!1 - 200` records `200` on its
/// own term; the outer complement has to union both, or taking the inherited
/// envelope alone drops the `200` and the reader decides a contract rustc rejects.
/// requires: true
/// ensures: y == !(!1 - 200)
pub fn contract_nested_complement_fold_operand_is_refused(y: i8) -> i8 {
    y
}

/// A named bound after a suffixed literal of the same bit pattern: `-128i8` records
/// the written magnitude `128`, and `i8::MIN` is the *same* eight-bit constant, so a
/// term-keyed envelope charged the literal's `128` to the bound and skipped this
/// valid contract. Both conjunct orders must read.
/// requires: y == -128i8 && y == i8::MIN
/// ensures: ret == y
pub fn contract_named_min_after_suffixed_min_reads(y: i8) -> i8 {
    y
}

/// The reverse conjunct order, so neither the literal nor the bound is recorded
/// first in a way that hides the collision.
/// requires: y == i8::MIN && y == -128i8
/// ensures: ret == y
pub fn contract_suffixed_min_after_named_min_reads(y: i8) -> i8 {
    y
}

/// The bare-literal form of the same collision: `128` is in range for a `u8` and
/// `i8::MIN` is valid, but both are the eight-bit constant `0x80`. The bound must
/// not inherit the literal's envelope in either order.
/// requires: x == 128 && y == i8::MIN
/// ensures: ret == 0
pub fn contract_named_min_after_bare_128_reads(x: u8, y: i8) -> u8 {
    let _ = (x, y);
    0
}

// ---------------------------------------------------------------------------
// Gap 8: a contract could not name a *tuple struct's* field.
// ---------------------------------------------------------------------------

/// A tuple struct, for the positional-field shapes.
///
/// `struct_head` recognised only a braced body, so `pub struct Pair(pub u8, pub u8)`
/// was never read as a struct: a contract naming `p.0` got "unknown name `p`"
/// because the argument's type was an opaque `Other("Pair")` with no layout. Its
/// fields are numbered by position, which is exactly the MIR field index, so
/// `p.0` and the body's `(*_1).0` name one variable.
pub struct Pair(pub u8, pub u8);

/// A one-field tuple struct with a *signed* field, so the field's signedness has
/// to come from the declared type rather than the dump. `Delta(-5)` is an `i8`
/// whose `.0` is negative, so `d.0 > -100` is a signed comparison.
pub struct Delta(pub i8);

/// The positional form of [`struct_reassign_then_field_read`]: a tuple struct's
/// field read through a reference.
/// requires: p.0 <= p.1
/// ensures: ret >= p.0
pub fn tuple_struct_reads_its_field(p: &Pair) -> u8 {
    if p.0 > p.1 { p.0 } else { p.1 }
}

/// The same contract on a *by-value* tuple struct, so the binding does not depend
/// on reading through the reference.
/// requires: p.0 <= p.1
/// ensures: ret <= p.1
pub fn tuple_struct_by_value_reads_its_field(p: Pair) -> u8 {
    if p.0 > p.1 { p.0 } else { p.1 }
}

/// A signed tuple field. `d.0 < 0` is satisfiable only under the *signed*
/// reading of the field, so a reader that took `d.0` as unsigned would find the
/// precondition unsatisfiable and refuse the contract as vacuous rather than
/// verify it. `verified` is therefore the evidence that the declared `i8` was
/// read, not the dump's unsigned default.
/// requires: d.0 < 0
/// ensures: ret < 0
pub fn tuple_struct_signed_field_reads(d: &Delta) -> i8 {
    d.0
}

/// A generic type whose method is monomorphised to `Wrapper<u8>`.
pub struct Wrapper<T> {
    pub v: T,
}

impl Wrapper<u8> {
    /// An associated function, called as `Wrapper::seed`.
    pub fn seed(v: u8) -> Wrapper<u8> {
        Wrapper { v }
    }

    /// A `&mut self` builder that returns `&mut Self`.
    pub fn stow(&mut self, x: u8) -> &mut Wrapper<u8> {
        self.v = x;
        self
    }

    /// A `&self` read.
    pub fn peek(&self) -> u8 {
        self.v
    }
}

/// A trait method call on a concrete receiver.
pub trait Stow {
    fn stash(&mut self, x: u8);
}

pub struct Slot {
    pub v: u8,
}

impl Stow for Slot {
    fn stash(&mut self, x: u8) {
        self.v = x;
    }
}

/// A method on a tuple struct.
pub struct Couple(pub u8, pub u8);

impl Couple {
    /// A `&self` read that names a positional field.
    pub fn prim(&self) -> u8 {
        self.0
    }

    /// A method taking an argument.
    pub fn shift_by(&self, k: u8) -> u8 {
        self.0 + k
    }
}

/// A generic method, monomorphised to `Wrapper<u8>`.
/// requires: true
/// ensures: ret == 5
pub fn a_generic_method(mut w: Wrapper<u8>) -> u8 {
    w.stow(5);
    w.v
}

/// An associated function, a `&mut self` builder and a `&self` read in one body.
/// requires: true
/// ensures: ret == 5
pub fn an_associated_fn_and_builder_chain() -> u8 {
    let mut w = Wrapper::seed(0);
    w.stow(5);
    w.peek()
}

/// A trait method call on a concrete receiver.
/// requires: true
/// ensures: ret == 5
pub fn a_trait_method(mut s: Slot) -> u8 {
    s.stash(5);
    s.v
}

/// A `&self` method on a tuple struct, naming a positional field.
/// requires: t.0 == 9
/// ensures: ret == 9
pub fn a_tuple_struct_read_method(t: Couple) -> u8 {
    t.prim()
}

/// A `&self` method taking an argument.
/// requires: t.0 == 3
/// ensures: ret == 7
pub fn a_method_with_an_argument(t: Couple) -> u8 {
    t.shift_by(4)
}

/// A *reborrow* target: `set_five(&mut *r)` where `r: &mut u8`.
///
/// The `&mut *r` names the place `r` already addresses, so the write belongs to the
/// caller's `x`, not to the local `r`. `resolve` collapses the deref, which is what
/// makes this one store.
/// requires: true
/// ensures: ret == 5
pub fn a_reborrow_target_reaches_the_caller(mut x: u8) -> u8 {
    let r = &mut x;
    set_five(&mut *r);
    x
}

/// The false direction of [`a_reborrow_target_reaches_the_caller`].
/// requires: x == 0
/// ensures: ret == 0
pub fn a_stale_reborrow_cannot_prove_this(mut x: u8) -> u8 {
    let r = &mut x;
    set_five(&mut *r);
    x
}

/// A write through a `&mut` to a *tuple component* target (`&mut t.0`).
/// requires: true
/// ensures: ret == 5
pub fn a_tuple_component_target_reaches_the_caller(mut t: Pair) -> u8 {
    set_five(&mut t.0);
    t.0
}

/// The false direction of [`a_tuple_component_target_reaches_the_caller`].
/// requires: t.0 == 0
/// ensures: ret == 0
pub fn a_stale_tuple_component_cannot_prove_this(mut t: Pair) -> u8 {
    set_five(&mut t.0);
    t.0
}

/// A helper that *reads* through a `&u8`. Before the referent's value was carried
/// into the callee, `_1` held the reference temp's `Unknown`, so `*v` was an
/// unmodelled operand and the caller could not be decided at all -- while a helper
/// that only *wrote* worked, because the write created the value the copy-back read.
pub fn read_through(v: &u8) -> u8 {
    *v
}

/// A helper that reads *and* writes through a `&mut u8`.
pub fn bump_through(v: &mut u8) {
    *v = *v + 1;
}

/// Two `&mut` to *different* fields of one struct, in a single call.
pub fn set_two(lo: &mut u8, hi: &mut u8) {
    *lo = 5;
    *hi = 7;
}

/// A swap through two `&mut`, the shape that *reads* both referents.
pub fn swap_two(lo: &mut u8, hi: &mut u8) {
    let t = *lo;
    *lo = *hi;
    *hi = t;
}

/// A helper that writes a *nested aggregate* it was handed (`&mut o.i`).
pub fn write_nested(i: &mut InnerBox) {
    i.v = 5;
}

/// A helper that *reads* a nested aggregate it was handed (`&InnerBox`).
pub fn read_nested(i: &InnerBox) -> u8 {
    i.v
}

/// A read through a helper's `&u8`.
/// requires: x == 3
/// ensures: ret == 3
pub fn a_read_through_a_helper(x: u8) -> u8 {
    read_through(&x)
}

/// The false direction of [`a_read_through_a_helper`].
/// requires: x == 3
/// ensures: ret == 4
pub fn a_stale_read_through_a_helper_cannot_prove_this(x: u8) -> u8 {
    read_through(&x)
}

/// A read-modify-write through a helper's `&mut u8`.
/// requires: x == 3
/// ensures: ret == 4
pub fn a_bump_through_a_helper(mut x: u8) -> u8 {
    bump_through(&mut x);
    x
}

/// The false direction of [`a_bump_through_a_helper`]: the bump must be visible.
/// requires: x == 3
/// ensures: ret == 3
pub fn a_stale_bump_cannot_prove_this(mut x: u8) -> u8 {
    bump_through(&mut x);
    x
}

/// Two `&mut` to different fields in one call, and the first field read back.
/// requires: true
/// ensures: ret == 5
pub fn two_reference_arguments(mut c: Config) -> u8 {
    set_two(&mut c.lo, &mut c.hi);
    c.lo
}

/// The *other* field of the same two-reference call.
/// requires: true
/// ensures: ret == 7
pub fn two_reference_arguments_other(mut c: Config) -> u8 {
    set_two(&mut c.lo, &mut c.hi);
    c.hi
}

/// The false direction: `hi` must not read `lo`'s value.
/// requires: true
/// ensures: ret == 5
pub fn two_reference_arguments_swapped_cannot_prove_this(mut c: Config) -> u8 {
    set_two(&mut c.lo, &mut c.hi);
    c.hi
}

/// A swap through two references: both fields are *read*, which is the case that
/// needs the referent's value carried into the callee, not just its parts.
/// requires: c.lo == 1 && c.hi == 2
/// ensures: ret == 2
pub fn a_swap_through_two_references(mut c: Config) -> u8 {
    swap_two(&mut c.lo, &mut c.hi);
    c.lo
}

/// The other half of the swap.
/// requires: c.lo == 1 && c.hi == 2
/// ensures: ret == 1
pub fn a_swap_through_two_references_other(mut c: Config) -> u8 {
    swap_two(&mut c.lo, &mut c.hi);
    c.hi
}

/// The false direction of the swap: `lo` must not still be 1.
/// requires: c.lo == 1 && c.hi == 2
/// ensures: ret == 1
pub fn a_stale_swap_cannot_prove_this(mut c: Config) -> u8 {
    swap_two(&mut c.lo, &mut c.hi);
    c.lo
}

/// A helper writing a nested aggregate target (`&mut o.i`) must land on `o.i.v`.
/// Before the copy-back was re-based on the target's projection, this write was
/// dropped: the true contract `ret == 5` was refuted and the false `ret == 0` was
/// **proved**.
/// requires: true
/// ensures: ret == 5
pub fn a_nested_aggregate_target_reaches(mut o: OuterBox) -> u8 {
    write_nested(&mut o.i);
    o.i.v
}

/// The false direction of [`a_nested_aggregate_target_reaches`] -- the one that was
/// wrongly proved before the re-basing.
/// requires: o.i.v == 0
/// ensures: ret == 0
pub fn a_stale_nested_aggregate_cannot_prove_this(mut o: OuterBox) -> u8 {
    write_nested(&mut o.i);
    o.i.v
}

/// A *read* of a nested aggregate target (`&o.i`).
/// requires: o.i.v == 3
/// ensures: ret == 3
pub fn a_nested_aggregate_read(o: OuterBox) -> u8 {
    read_nested(&o.i)
}

/// The false direction of [`a_nested_aggregate_read`].
/// requires: o.i.v == 3
/// ensures: ret == 4
pub fn a_stale_nested_aggregate_read_cannot_prove_this(o: OuterBox) -> u8 {
    read_nested(&o.i)
}

/// A `&mut self` method on the *inner* type, called on a nested-field receiver
/// (`o.i.set_leaf(5)`), plus its `&self` read.
impl InnerBox {
    /// A `&mut self` method writing the leaf.
    pub fn set_leaf(&mut self, x: u8) {
        self.v = x;
    }

    /// A `&self` method reading the leaf.
    pub fn get_leaf(&self) -> u8 {
        self.v
    }
}

/// A method on a *nested-field* receiver: `o.i.set_leaf(5)`.
/// requires: true
/// ensures: ret == 5
pub fn a_method_on_a_nested_receiver(mut o: OuterBox) -> u8 {
    o.i.set_leaf(5);
    o.i.v
}

/// The false direction of [`a_method_on_a_nested_receiver`].
/// requires: o.i.v == 0
/// ensures: ret == 0
pub fn a_stale_nested_receiver_cannot_prove_this(mut o: OuterBox) -> u8 {
    o.i.set_leaf(5);
    o.i.v
}

/// Two method calls in sequence on one receiver: the later write must win.
/// requires: true
/// ensures: ret == 7
pub fn two_methods_in_sequence(mut o: OuterBox) -> u8 {
    o.i.set_leaf(5);
    o.i.set_leaf(7);
    o.i.v
}

/// The false direction: the first call's 5 must not survive.
/// requires: true
/// ensures: ret == 5
pub fn a_stale_first_method_cannot_prove_this(mut o: OuterBox) -> u8 {
    o.i.set_leaf(5);
    o.i.set_leaf(7);
    o.i.v
}

/// A method call through a *reborrowed* receiver (`let r = &mut o; r.i.set_leaf(5)`).
/// requires: true
/// ensures: ret == 5
pub fn a_method_through_a_reborrow(mut o: OuterBox) -> u8 {
    let r = &mut o;
    r.i.set_leaf(5);
    o.i.v
}

/// The false direction of [`a_method_through_a_reborrow`].
/// requires: o.i.v == 0
/// ensures: ret == 0
pub fn a_stale_reborrow_receiver_cannot_prove_this(mut o: OuterBox) -> u8 {
    let r = &mut o;
    r.i.set_leaf(5);
    o.i.v
}

/// A `&self` method whose result feeds a `&mut` write on the same struct.
/// requires: o.i.v == 9
/// ensures: ret == 9
pub fn a_read_method_feeds_a_write(mut o: OuterBox) -> u8 {
    let t = o.i.get_leaf();
    o.i.set_leaf(t);
    o.i.v
}

/// The false direction of [`a_read_method_feeds_a_write`].
/// requires: o.i.v == 9
/// ensures: ret == 8
pub fn a_stale_read_method_cannot_prove_this(mut o: OuterBox) -> u8 {
    let t = o.i.get_leaf();
    o.i.set_leaf(t);
    o.i.v
}

/// A two-leaf type for the sibling test, kept apart from `InnerBox` so the leaf
/// write and the sibling read are fields of one target.
pub struct DuoBox {
    pub v: u8,
    pub w: u8,
}

/// A helper writing only the `v` leaf of a `&mut DuoBox`.
pub fn write_duo(d: &mut DuoBox) {
    d.v = 5;
}

/// A leaf write through a `&mut` target leaves the target's *sibling* leaf at the
/// caller's seed.
/// requires: d.w == 9
/// ensures: ret == 9
pub fn a_leaf_write_leaves_its_sibling(mut d: DuoBox) -> u8 {
    write_duo(&mut d);
    d.w
}

/// The false direction of [`a_leaf_write_leaves_its_sibling`]: the sibling is not
/// the value that was written.
/// requires: d.w == 9
/// ensures: ret == 5
pub fn a_stale_leaf_sibling_cannot_prove_this(mut d: DuoBox) -> u8 {
    write_duo(&mut d);
    d.w
}

/// A helper writing the constant one through a `&mut u8`.
pub fn write_one(v: &mut u8) {
    *v = 1;
}

/// A helper returning a `&mut` to a tuple component.
pub fn tuple_mut(t: &mut (u8, u8)) -> &mut u8 {
    &mut t.0
}

/// An inner helper that writes through a `&mut u8`.
pub fn relay_set(v: &mut u8, x: u8) {
    *v = x;
}

/// An outer helper that *forwards* its `&mut u8` to the inner one.
pub fn pass_on(v: &mut u8, x: u8) {
    relay_set(v, x);
}

/// An outer helper that forwards a constant to the inner one.
pub fn pass_on_five(v: &mut u8) {
    relay_set(v, 5);
}

/// A helper that *returns* the reference it was given. The caller's `let r =
/// identity(&mut x); *r = 5` needs the returned reference's address to survive the
/// call: before it did, `*r = 5` was a write to a local no caller reads, the write
/// was dropped, and the false `ret == 0` was **proved** while the true `ret == 5`
/// was refuted.
pub fn borrowed_identity(x: &mut u8) -> &mut u8 {
    x
}

/// A two-frame chain: the caller's write goes through `pass_on` into `relay_set`.
/// requires: true
/// ensures: ret == 5
pub fn a_two_frame_chain(mut x: u8) -> u8 {
    pass_on(&mut x, 5);
    x
}

/// The false direction of [`a_two_frame_chain`].
/// requires: x == 0
/// ensures: ret == 0
pub fn a_stale_two_frame_chain_cannot_prove_this(mut x: u8) -> u8 {
    pass_on(&mut x, 5);
    x
}

/// A two-frame chain whose inner write is a constant.
/// requires: true
/// ensures: ret == 5
pub fn a_two_frame_constant(mut x: u8) -> u8 {
    pass_on_five(&mut x);
    x
}

/// The false direction of [`a_two_frame_constant`].
/// requires: x == 0
/// ensures: ret == 0
pub fn a_stale_two_frame_constant_cannot_prove_this(mut x: u8) -> u8 {
    pass_on_five(&mut x);
    x
}

/// A write through a reference *returned* by a helper.
/// requires: true
/// ensures: ret == 5
pub fn a_write_through_a_returned_reference(mut x: u8) -> u8 {
    let r = borrowed_identity(&mut x);
    *r = 5;
    x
}

/// The false direction of [`a_write_through_a_returned_reference`] -- the one that
/// was wrongly proved before the returned reference kept its address.
/// requires: x == 0
/// ensures: ret == 0
pub fn a_stale_returned_reference_cannot_prove_this(mut x: u8) -> u8 {
    let r = borrowed_identity(&mut x);
    *r = 5;
    x
}

/// Methods that *return* a reference to one of their own fields.
impl Config {
    /// A `&mut self` method returning a `&mut` to the `lo` field.
    pub fn lo_mut(&mut self) -> &mut u8 {
        &mut self.lo
    }

    /// The same for `hi`.
    pub fn hi_mut(&mut self) -> &mut u8 {
        &mut self.hi
    }

    /// A builder that writes and returns `&mut Self`.
    pub fn touch(&mut self, x: u8) -> &mut Config {
        self.lo = x;
        self
    }
}

/// A write through a `&mut` to a field *returned by a method*: `*c.lo_mut() = 5`.
///
/// The returned reference names a place in the *callee's* terms (`&mut (*_1).0`),
/// and `_1` is the caller's `c`, so the write belongs to `c.lo`. Without that
/// translation the returned reference named nothing, the write was dropped, the true
/// `ret == 5` was refuted, and the false `ret == 0` was **proved**.
/// requires: true
/// ensures: ret == 5
pub fn a_write_through_a_returned_field_reference(mut c: Config) -> u8 {
    *c.lo_mut() = 5;
    c.lo
}

/// The false direction of [`a_write_through_a_returned_field_reference`] -- the one
/// that was wrongly proved.
/// requires: c.lo == 0
/// ensures: ret == 0
pub fn a_stale_returned_field_reference_cannot_prove_this(mut c: Config) -> u8 {
    *c.lo_mut() = 5;
    c.lo
}

/// The same for the *other* field, so the translation cannot be a coincidence of one
/// index.
/// requires: true
/// ensures: ret == 7
pub fn a_write_through_the_other_returned_reference(mut c: Config) -> u8 {
    *c.hi_mut() = 7;
    c.hi
}

/// The false direction of [`a_write_through_the_other_returned_reference`].
/// requires: c.hi == 0
/// ensures: ret == 0
pub fn a_stale_other_returned_reference_cannot_prove_this(mut c: Config) -> u8 {
    *c.hi_mut() = 7;
    c.hi
}

/// A builder whose returned `&mut Self` is read back.
/// requires: true
/// ensures: ret == 9
pub fn a_write_through_a_returned_builder(mut c: Config) -> u8 {
    c.touch(9);
    c.lo
}

/// The false direction of [`a_write_through_a_returned_builder`].
/// requires: c.lo == 0
/// ensures: ret == 0
pub fn a_stale_returned_builder_cannot_prove_this(mut c: Config) -> u8 {
    c.touch(9);
    c.lo
}

/// A free function returning a `&mut` to a *nested* field of its argument.
pub fn nested_mut(o: &mut OuterBox) -> &mut u8 {
    &mut o.i.v
}

/// A free function returning a `&mut` to a field of its *second* argument.
pub fn pick_second<'a>(_a: &'a mut OuterBox, b: &'a mut InnerBox) -> &'a mut u8 {
    &mut b.v
}

/// A `&mut self` method returning a `&mut` to a nested field.
impl OuterBox {
    /// A `&mut self` method returning `&mut` to `self.i.v`.
    pub fn inner_mut(&mut self) -> &mut u8 {
        &mut self.i.v
    }
}

/// A write through a `&mut` to a *nested* field returned by a helper: the returned
/// place is two steps deep in the caller (`o.i.v`), so the translation has to carry
/// the whole projection, not just the head local.
/// requires: true
/// ensures: ret == 5
pub fn a_write_through_a_returned_nested_reference(mut o: OuterBox) -> u8 {
    *nested_mut(&mut o) = 5;
    o.i.v
}

/// The false direction of [`a_write_through_a_returned_nested_reference`].
/// requires: o.i.v == 0
/// ensures: ret == 0
pub fn a_stale_returned_nested_reference_cannot_prove_this(mut o: OuterBox) -> u8 {
    *nested_mut(&mut o) = 5;
    o.i.v
}

/// A write to `o.i.v` must leave `o.j.v` alone.
/// requires: o.j.v == 3
/// ensures: ret == 3
pub fn a_returned_nested_reference_leaves_its_sibling(mut o: OuterBox) -> u8 {
    *nested_mut(&mut o) = 5;
    o.j.v
}

/// The same through a *method* returning `&mut self.i.v`.
/// requires: true
/// ensures: ret == 5
pub fn a_write_through_a_method_nested_reference(mut o: OuterBox) -> u8 {
    *o.inner_mut() = 5;
    o.i.v
}

/// The false direction of [`a_write_through_a_method_nested_reference`].
/// requires: o.i.v == 0
/// ensures: ret == 0
pub fn a_stale_method_nested_reference_cannot_prove_this(mut o: OuterBox) -> u8 {
    *o.inner_mut() = 5;
    o.i.v
}

/// A returned reference to the *second* argument, so the translation must pick the
/// right argument and not the first.
/// requires: true
/// ensures: ret == 5
pub fn a_write_through_a_second_argument_reference(mut a: OuterBox, mut b: InnerBox) -> u8 {
    *pick_second(&mut a, &mut b) = 5;
    b.v
}

/// The false direction of [`a_write_through_a_second_argument_reference`].
/// requires: b.v == 0
/// ensures: ret == 0
pub fn a_stale_second_argument_reference_cannot_prove_this(mut a: OuterBox, mut b: InnerBox) -> u8 {
    *pick_second(&mut a, &mut b) = 5;
    b.v
}

/// A reference returned by one call, passed straight into another.
/// requires: true
/// ensures: ret == 1
pub fn a_reference_returned_into_another_call(mut c: Config) -> u8 {
    write_one(borrowed_identity(&mut c.lo));
    c.lo
}

/// The false direction of [`a_reference_returned_into_another_call`].
/// requires: c.lo == 0
/// ensures: ret == 0
pub fn a_stale_returned_into_another_call_cannot_prove_this(mut c: Config) -> u8 {
    write_one(borrowed_identity(&mut c.lo));
    c.lo
}

/// A reborrow of a returned reference.
/// requires: true
/// ensures: ret == 5
pub fn a_reborrow_of_a_returned_reference(mut x: u8) -> u8 {
    let r = borrowed_identity(&mut x);
    let s = &mut *r;
    *s = 5;
    x
}

/// The false direction of [`a_reborrow_of_a_returned_reference`].
/// requires: x == 0
/// ensures: ret == 0
pub fn a_stale_reborrow_of_a_returned_reference_cannot_prove_this(mut x: u8) -> u8 {
    let r = borrowed_identity(&mut x);
    let s = &mut *r;
    *s = 5;
    x
}

/// Two returned references to *different* fields, both written, and the first read.
/// requires: true
/// ensures: ret == 5
pub fn two_returned_field_references(mut c: Config) -> u8 {
    let r = borrowed_identity(&mut c.lo);
    let s = borrowed_identity(&mut c.hi);
    *r = 5;
    *s = 7;
    c.lo
}

/// The false direction of [`two_returned_field_references`]: the *other* field's
/// write must not land on `lo`.
/// requires: true
/// ensures: ret == 7
pub fn a_stale_two_returned_fields_cannot_prove_this(mut c: Config) -> u8 {
    let r = borrowed_identity(&mut c.lo);
    let s = borrowed_identity(&mut c.hi);
    *r = 5;
    *s = 7;
    c.lo
}

/// A returned reference to a *tuple component*.
/// requires: true
/// ensures: ret == 5
pub fn a_returned_tuple_component_reference(mut t: (u8, u8)) -> u8 {
    *tuple_mut(&mut t) = 5;
    t.0
}

/// The false direction of [`a_returned_tuple_component_reference`].
/// requires: true
/// ensures: ret == 0
pub fn a_stale_tuple_component_reference_cannot_prove_this(mut t: (u8, u8)) -> u8 {
    *tuple_mut(&mut t) = 5;
    t.0
}

/// A helper writing two *different aggregate* fields through two `&mut`.
pub fn set_two_parts(a: &mut InnerBox, b: &mut InnerBox) {
    a.v = 5;
    b.v = 7;
}

/// The same two fields, swapped: both referents are *read*.
pub fn swap_two_parts(a: &mut InnerBox, b: &mut InnerBox) {
    let t = a.v;
    a.v = b.v;
    b.v = t;
}

/// A helper writing two *elements* of one array through one `&mut`.
pub fn set_two_elements(a: &mut [u8; 2]) {
    a[0] = 5;
    a[1] = 7;
}

/// The same two elements, swapped.
pub fn swap_two_elements(a: &mut [u8; 2]) {
    let t = a[0];
    a[0] = a[1];
    a[1] = t;
}

/// Two `&mut` to different *aggregate* fields in one call, and the first read back.
/// requires: true
/// ensures: ret == 5
pub fn two_aggregate_reference_targets(mut o: OuterBox) -> u8 {
    set_two_parts(&mut o.i, &mut o.j);
    o.i.v
}

/// The *other* aggregate field of the same call.
/// requires: true
/// ensures: ret == 7
pub fn two_aggregate_reference_targets_other(mut o: OuterBox) -> u8 {
    set_two_parts(&mut o.i, &mut o.j);
    o.j.v
}

/// The false direction: the two aggregate writes must not collapse onto one.
/// requires: true
/// ensures: ret == 7
pub fn a_stale_two_aggregate_targets_cannot_prove_this(mut o: OuterBox) -> u8 {
    set_two_parts(&mut o.i, &mut o.j);
    o.i.v
}

/// A swap of two aggregate fields, so both referents are read.
/// requires: o.i.v == 1 && o.j.v == 2
/// ensures: ret == 2
pub fn a_swap_of_two_aggregate_targets(mut o: OuterBox) -> u8 {
    swap_two_parts(&mut o.i, &mut o.j);
    o.i.v
}

/// The false direction of [`a_swap_of_two_aggregate_targets`].
/// requires: o.i.v == 1 && o.j.v == 2
/// ensures: ret == 1
pub fn a_stale_swap_of_aggregate_targets_cannot_prove_this(mut o: OuterBox) -> u8 {
    swap_two_parts(&mut o.i, &mut o.j);
    o.i.v
}

/// Two element writes through one `&mut` to the whole array, first element read.
/// requires: true
/// ensures: ret == 5
pub fn two_elements_through_one_reference(mut a: [u8; 2]) -> u8 {
    set_two_elements(&mut a);
    a[0]
}

/// The *other* element of the same call.
/// requires: true
/// ensures: ret == 7
pub fn two_elements_through_one_reference_other(mut a: [u8; 2]) -> u8 {
    set_two_elements(&mut a);
    a[1]
}

/// The false direction: the two element writes must not collapse onto one.
/// requires: true
/// ensures: ret == 7
pub fn a_stale_two_elements_cannot_prove_this(mut a: [u8; 2]) -> u8 {
    set_two_elements(&mut a);
    a[0]
}

/// An element swap through a `&mut` to the whole array.
/// requires: a[0] == 1 && a[1] == 2
/// ensures: ret == 2
pub fn a_swap_of_two_elements(mut a: [u8; 2]) -> u8 {
    swap_two_elements(&mut a);
    a[0]
}

/// The false direction of [`a_swap_of_two_elements`].
/// requires: a[0] == 1 && a[1] == 2
/// ensures: ret == 1
pub fn a_stale_swap_of_elements_cannot_prove_this(mut a: [u8; 2]) -> u8 {
    swap_two_elements(&mut a);
    a[0]
}

/// A helper reading a *scalar* field of a `&DuoBox`.
pub fn take_duo_v(d: &DuoBox) -> u8 {
    d.v
}

/// A helper writing a *scalar* field through a `&mut DuoBox`.
pub fn put_duo_v(d: &mut DuoBox, x: u8) {
    d.v = x;
}

/// A scalar field read through a helper's `&DuoBox`: the referent's parts are
/// carried in, and the callee's read of `d.v` resolves to the caller's `d.v`.
/// requires: d.v == 7
/// ensures: ret == 7
pub fn a_scalar_field_read_through_a_reference(d: DuoBox) -> u8 {
    take_duo_v(&d)
}

/// The false direction of [`a_scalar_field_read_through_a_reference`].
/// requires: d.v == 7
/// ensures: ret == 0
pub fn a_stale_scalar_field_read_cannot_prove_this(d: DuoBox) -> u8 {
    take_duo_v(&d)
}

/// A scalar field written through a helper's `&mut DuoBox`.
/// requires: true
/// ensures: ret == 5
pub fn a_scalar_field_write_through_a_reference(mut d: DuoBox) -> u8 {
    put_duo_v(&mut d, 5);
    d.v
}

/// The false direction of [`a_scalar_field_write_through_a_reference`].
/// requires: d.v == 0
/// ensures: ret == 0
pub fn a_stale_scalar_field_write_cannot_prove_this(mut d: DuoBox) -> u8 {
    put_duo_v(&mut d, 5);
    d.v
}

/// A write through *two* levels of `&mut`: `**rr = 5` on a `&mut &mut u8`.
///
/// Lowers to `_4 = no_retag copy (*_3); (*_4) = 5`, where `_4` is a `&mut u8`. The
/// `no_retag` prefix made the rvalue unparseable, and the copy of a reference
/// *through* a deref had no branch, so `_4` got no address and the write was dropped:
/// the false `ret == 0` was proved against a body that returns 5, and the true
/// `ret == 5` was refuted.
/// requires: true
/// ensures: ret == 5
pub fn a_write_through_two_levels_of_reference(mut x: u8) -> u8 {
    let mut r = &mut x;
    let rr = &mut r;
    **rr = 5;
    x
}

/// The false direction of [`a_write_through_two_levels_of_reference`]: if the write
/// were dropped, this would verify.
/// requires: x == 0
/// ensures: ret == 0
pub fn a_stale_two_level_write_cannot_prove_this(mut x: u8) -> u8 {
    let mut r = &mut x;
    let rr = &mut r;
    **rr = 5;
    x
}

/// A *read* through two levels of reference: `**rr`.
/// requires: x == 3
/// ensures: ret == 3
pub fn a_read_through_two_levels_of_reference(x: u8) -> u8 {
    let r = &x;
    let rr = &r;
    **rr
}

/// The false direction of [`a_read_through_two_levels_of_reference`].
/// requires: x == 3
/// ensures: ret == 4
pub fn a_stale_two_level_read_cannot_prove_this(x: u8) -> u8 {
    let r = &x;
    let rr = &r;
    **rr
}

/// A write through a reference to a *local copy* must not reach the original.
/// requires: x == 3
/// ensures: ret == 3
pub fn a_write_to_a_copy_stays_in_the_copy(x: u8) -> u8 {
    let mut y = x;
    let r = &mut y;
    *r = 9;
    x
}

/// The false direction of [`a_write_to_a_copy_stays_in_the_copy`]: if the copy
/// aliased the original, this would verify.
/// requires: x == 3
/// ensures: ret == 9
pub fn a_stale_copy_write_cannot_prove_this(x: u8) -> u8 {
    let mut y = x;
    let r = &mut y;
    *r = 9;
    x
}

/// A copy from one reference target to another: `*r = *s` where the two point at
/// different fields.
/// requires: c.lo == 1 && c.hi == 2
/// ensures: ret == 2
pub fn a_copy_between_two_reference_targets(mut c: Config) -> u8 {
    let r = &mut c.lo;
    let s = &mut c.hi;
    *r = *s;
    c.lo
}

/// The false direction of [`a_copy_between_two_reference_targets`]: if the copy
/// went the wrong way, or `*s` read the stale `lo`, this would verify.
/// requires: c.lo == 1 && c.hi == 2
/// ensures: ret == 1
pub fn a_stale_copy_between_reference_targets_cannot_prove_this(mut c: Config) -> u8 {
    let r = &mut c.lo;
    let s = &mut c.hi;
    *r = *s;
    c.lo
}

/// A field written through a *double* reference to a struct: `(**rr).lo = 5`.
///
/// The `*` chain is local, so both levels resolve inside the frame; it is the
/// *argument* case (`relay(&mut r)` with `v: &mut &mut u8`) that crosses frames and
/// is refused.
/// requires: true
/// ensures: ret == 5
pub fn a_write_through_a_double_reference_to_a_struct(mut c: Config) -> u8 {
    let mut r = &mut c;
    let rr = &mut r;
    (**rr).lo = 5;
    c.lo
}

/// The false direction of [`a_write_through_a_double_reference_to_a_struct`].
/// requires: c.lo == 0
/// ensures: ret == 0
pub fn a_stale_double_reference_struct_cannot_prove_this(mut c: Config) -> u8 {
    let mut r = &mut c;
    let rr = &mut r;
    (**rr).lo = 5;
    c.lo
}

/// A call through a reference to a reference is *refused*, not modelled.
///
/// `relay(&mut r)` with `relay(v: &mut &mut u8) { **v = 5 }` crosses two frames: the
/// outer referent lives in the caller and the callee reaches it with its own local
/// index. The write was dropped, so the false `ret == 0` was **proved**; refusing
/// leaves the true contract unproved instead.
/// requires: true
/// ensures: ret == 5
pub fn a_call_through_a_reference_to_a_reference_is_refused(mut x: u8) -> u8 {
    let mut r = &mut x;
    relay_two(&mut r);
    x
}

/// A helper writing through a reference to a reference.
pub fn relay_two(v: &mut &mut u8) {
    **v = 5;
}

/// A helper whose own `ensures` is false: the body returns 3, not 5.
///
/// Its purpose is the *caller* below. Assuming a callee's `ensures` instead of
/// inlining its body is the canonical way a verifier proves a false contract, so
/// this pair pins the property that the frontend never does.
/// requires: true
/// ensures: ret == 5
pub fn a_helper_whose_contract_is_false() -> u8 {
    3
}

/// The caller of [`a_helper_whose_contract_is_false`]. If the callee's `ensures`
/// were assumed rather than its body inlined, this false contract would verify.
/// requires: true
/// ensures: ret == 5
pub fn a_caller_of_a_lying_helper_cannot_prove_this() -> u8 {
    a_helper_whose_contract_is_false()
}

/// The same call with the contract the body actually satisfies, so the *shape* is
/// shown to be decidable and only the false direction fails.
/// requires: true
/// ensures: ret == 3
pub fn a_caller_of_a_lying_helper_knows_the_truth() -> u8 {
    a_helper_whose_contract_is_false()
}

/// A helper with an unsatisfiable precondition.
/// requires: x == 99
/// ensures: ret == x
pub fn a_helper_that_needs_99(x: u8) -> u8 {
    x
}

/// A call that violates its callee's precondition.
///
/// This one *verifies*, and that is the honest answer rather than a false proof:
/// a callee's `requires` is not turned into an obligation at the call site, the
/// body is inlined instead, and `needs_99` returns its argument whatever it is, so
/// `ret == 7` really does hold. The name says `_is_not_checked` rather than
/// `_cannot_prove_this` because this entry is *not* a false-direction probe and
/// must not be counted as one.
/// requires: true
/// ensures: ret == 7
pub fn a_call_that_violates_a_precondition_is_not_checked() -> u8 {
    a_helper_that_needs_99(7)
}

/// A helper whose precondition rules out zero, so its division is safe.
/// requires: x != 0
/// ensures: ret == 10 / x
pub fn a_helper_that_divides_ten(x: u8) -> u8 {
    10 / x
}

/// The same call-site violation, but where the callee's body *panics* on the
/// violated input. Inlining the body is what catches this: the division by zero
/// is an obligation of the inlined path, so the false `ret == 5` fails on a panic
/// rather than verifying. This is why "the precondition is not checked at the
/// call site" is sound-incomplete and not unsound.
/// requires: true
/// ensures: ret == 5
pub fn a_call_that_divides_by_zero_cannot_prove_this() -> u8 {
    a_helper_that_divides_ten(0)
}

/// A helper with an *unsatisfiable* precondition and a postcondition that is false
/// for its body.
///
/// The dangerous shape: a verifier that reads "the precondition is vacuous, so the
/// contract holds trivially" may then assume `ret == 99` after any call. The body
/// returns its argument, so that assumption is a false proof.
/// requires: x > 200 && x < 10
/// ensures: ret == 99
pub fn a_vacuous_helper_whose_postcondition_is_false(x: u8) -> u8 {
    x
}

/// The caller of [`a_vacuous_helper_whose_postcondition_is_false`]. If the callee's
/// postcondition were assumed, this false contract would verify.
/// requires: true
/// ensures: ret == 99
pub fn a_caller_inheriting_a_vacuous_lie_cannot_prove_this() -> u8 {
    a_vacuous_helper_whose_postcondition_is_false(0)
}

/// The honest direction of the same call: what the body actually returns.
/// requires: true
/// ensures: ret == 0
pub fn a_caller_of_a_vacuous_helper_knows_the_truth() -> u8 {
    a_vacuous_helper_whose_postcondition_is_false(0)
}

/// Recursion whose contract is false. Assuming the recursive call's postcondition
/// is the inductive step of a false proof.
/// requires: true
/// ensures: ret == 0
pub fn a_recursive_contract_that_is_false_cannot_prove_this(n: u8) -> u8 {
    if n == 0 { 0 } else { a_recursive_contract_that_is_false_cannot_prove_this(n - 1) + 1 }
}

/// One half of a mutually recursive pair whose contracts are false.
/// requires: true
/// ensures: ret == 0
pub fn a_mutual_lie_a_cannot_prove_this(n: u8) -> u8 {
    if n == 0 { 0 } else { a_mutual_lie_b_cannot_prove_this(n - 1) + 1 }
}

/// The other half of the mutually recursive pair.
/// requires: true
/// ensures: ret == 0
pub fn a_mutual_lie_b_cannot_prove_this(n: u8) -> u8 {
    if n == 0 { 0 } else { a_mutual_lie_a_cannot_prove_this(n - 1) + 1 }
}

/// A recursive function proved by induction on a `decreases:` measure.
///
/// The self-call is *not* inlined. It is answered by this very contract: the
/// precondition is proved of `n - 1`, the measure `n` is proved to shrink, and
/// the postcondition is then assumed for the result. The base case (`n == 0`)
/// is proved by the body itself, which is what stops the assumption from being
/// circular. Before `decreases:` existed this function hit the inline-depth
/// bound and was reported incomplete.
/// requires: true
/// decreases: n
/// ensures: ret == n
pub fn a_recursive_identity(n: u8) -> u8 {
    if n == 0 { 0 } else { a_recursive_identity(n - 1) + 1 }
}

/// A recursive function whose *base case* does not establish the postcondition,
/// so the induction must not save it.
///
/// `a_recursive_identity`'s twin: the recursive case is right, but the base case
/// returns `1` where the contract says `ret == n`, i.e. `ret == 0`. Nothing is
/// assumed at the base case -- only the body is checked there -- so this is the
/// one place a circular induction would go wrong. It must FAIL on the
/// postcondition, with a witness (`n == 0`).
/// requires: true
/// decreases: n
/// ensures: ret == n
pub fn a_recursive_lie_cannot_prove_this(n: u8) -> u8 {
    if n == 0 { 1 } else { a_recursive_lie_cannot_prove_this(n - 1) + 1 }
}

/// A recursive function whose measure does *not* decrease: the call is on the
/// same `n`, so the induction has no well-founded basis.
///
/// The precondition and the postcondition are both true of the body, so nothing
/// but the measure check stops this from being assumed. It must not verify: an
/// assumption without a decreasing measure is circular.
/// requires: true
/// decreases: n
/// ensures: ret == 0
pub fn a_recursive_call_that_does_not_decrease_cannot_prove_this(n: u8) -> u8 {
    if n == 0 { 0 } else { a_recursive_call_that_does_not_decrease_cannot_prove_this(n) }
}

/// A recursive function whose recursive call violates its own precondition.
///
/// The precondition `n <= 3` is what bounds the recursion, and the call is on
/// `n + 1`, which leaves that range. Proving the precondition of the call is
/// what makes the induction hypothesis applicable only where it holds; without
/// that check the postcondition would be assumed for an input the contract never
/// promised anything about.
/// requires: n <= 3
/// decreases: n
/// ensures: ret == 0
pub fn a_recursive_call_out_of_range_cannot_prove_this(n: u8) -> u8 {
    if n == 0 { 0 } else { a_recursive_call_out_of_range_cannot_prove_this(n + 1) }
}

/// An invariant that is false where the loop is entered. Checking initiation is
/// what stops an arbitrary induction hypothesis being taken on faith.
/// requires: n <= 3
/// invariant: i == 5
/// ensures: ret <= 3
pub fn an_invariant_false_on_entry_cannot_prove_this(n: u8) -> u8 {
    let mut i = 0u8;
    while i < n { i += 1; }
    i
}

/// An invariant the body does not preserve. Checking preservation is the other
/// half of the induction.
/// requires: n <= 3
/// invariant: i == 0
/// ensures: ret == 0
pub fn an_invariant_not_preserved_cannot_prove_this(n: u8) -> u8 {
    let mut i = 0u8;
    while i < n { i += 1; }
    i
}

/// A variable shift whose amount is *wider* than the value, which is the shape
/// rustc prints: the amount of `a >> b` may be any integer type.
///
/// This was `incomplete` until the barrel shifter read the amount at its own
/// width: the stages built their mask at the *value's* width, so `n & mask` mixed
/// 32 bits with 8 and the query came back ill-formed. Only the symbolic path
/// noticed, because `evaluate` folds an ill-formed term anyway -- so a proof about
/// a shift by a `u32` was refused while the same shift by a `u8` went through.
/// requires: a == 255 && b == 1
/// ensures: ret == 127
pub fn a_shift_by_a_wider_amount(a: u8, b: u32) -> u8 {
    a >> b
}

/// The false direction of [`a_shift_by_a_wider_amount`]: a logical right shift of
/// `255` by one is `127`, never `128`.
/// requires: a == 255 && b == 1
/// ensures: ret == 128
pub fn a_shift_by_a_wider_amount_cannot_prove_this(a: u8, b: u32) -> u8 {
    a >> b
}

/// An arithmetic right shift of a signed value, at a wider amount: `-1 >> 1` is
/// `-1` because the sign bit is replicated, not `127`.
/// requires: a == -1 && b == 1
/// ensures: ret == -1
pub fn an_arithmetic_shift_by_a_wider_amount(a: i8, b: u32) -> i8 {
    a >> b
}

/// The false direction: a *logical* shift of `-1` by one would be `127`.
/// requires: a == -1 && b == 1
/// ensures: ret == 127
pub fn an_arithmetic_shift_by_a_wider_amount_cannot_prove_this(a: i8, b: u32) -> i8 {
    a >> b
}

/// A constant operand makes the multiply-overflow test exact without a `2w`-bit
/// multiplier, so it decides at widths the general path refuses.
///
/// `a * 2` at `u32` was `incomplete` -- the general path widens to `2w` and gives
/// up past 16 bits -- while the same expression at `u8` verified. With one operand
/// a constant, `x * c` wraps exactly when `x > MAX / c`, which is one comparison
/// against a compile-time constant. An index scaled by an element size is the
/// shape this is for, and it is usually `usize`.
/// requires: a == 3
/// ensures: ret == 6
pub fn a_constant_multiply_of_a_wide_unsigned(a: u32) -> u32 {
    a * 2
}

/// The false direction of [`a_constant_multiply_of_a_wide_unsigned`].
/// requires: a == 3
/// ensures: ret == 7
pub fn a_constant_multiply_of_a_wide_unsigned_cannot_prove_this(a: u32) -> u32 {
    a * 2
}

/// The constant on the *left* must behave the same as on the right.
/// requires: a == 3
/// ensures: ret == 6
pub fn a_constant_multiply_with_the_constant_on_the_left(a: u32) -> u32 {
    2 * a
}

/// A scaled index: the element size is the constant and the type is `usize`.
/// requires: a == 3
/// ensures: ret == 24
pub fn a_scaled_index(a: usize) -> usize {
    a * 8
}

/// The false direction of [`a_scaled_index`].
/// requires: a == 3
/// ensures: ret == 25
pub fn a_scaled_index_cannot_prove_this(a: usize) -> usize {
    a * 8
}

/// The last value that does *not* wrap: `ceil(2^32 / 2) - 1`, where the product is
/// `2^32 - 2`. This is the boundary that separates an exact predicate from a
/// merely sufficient one.
/// requires: a == 2147483647
/// ensures: ret == 4294967294
pub fn a_constant_multiply_at_the_last_safe_value(a: u32) -> u32 {
    a * 2
}

/// One past that boundary: the product is `2^32`, so the multiply wraps and rustc's
/// `assert` must fail. A predicate that were too weak here would call this
/// panic-free, which is the failure mode that reports a *better* result than the
/// truth.
/// requires: a == 2147483648
/// ensures: ret == 0
pub fn a_constant_multiply_that_overflows_cannot_prove_this(a: u32) -> u32 {
    a * 2
}

/// Multiplying by zero cannot wrap, even at the type's maximum.
/// requires: a == 4294967295
/// ensures: ret == 0
pub fn a_constant_multiply_by_zero_never_overflows(a: u32) -> u32 {
    a * 0
}

/// Multiplying by one cannot wrap either, and this is the case where `MAX / c`
/// itself would not fit -- so it is decided by a constant `false` rather than by a
/// comparison.
/// requires: a == 4294967295
/// ensures: ret == 4294967295
pub fn a_constant_multiply_by_one_never_overflows(a: u32) -> u32 {
    a * 1
}

/// The false direction of [`a_constant_multiply_by_one_never_overflows`].
/// requires: a == 4294967295
/// ensures: ret == 0
pub fn a_constant_multiply_by_one_cannot_prove_this(a: u32) -> u32 {
    a * 1
}

/// A *signed* constant multiply is decided too, once the constant arm makes the
/// widened product a sum of shifts instead of a `2w`-bit schoolbook multiply.
///
/// This was `incomplete` and its name said so. The signed condition has one case per
/// combination of the three signs, so the arm is what made it affordable rather than
/// any change to the predicate -- the predicate was already exact, and only the width
/// bound stood in the way.
/// requires: a == 3
/// ensures: ret == 6
pub fn a_signed_constant_multiply_of_a_wide_value(a: i32) -> i32 {
    a * 2
}

/// The false direction of [`a_signed_constant_multiply_of_a_wide_value`].
/// requires: a == 3
/// ensures: ret == 7
pub fn a_signed_constant_multiply_of_a_wide_value_cannot_prove_this(a: i32) -> i32 {
    a * 2
}

/// The signed multiply *at `i64`* is decided, which is the case the `2w`-bit widening
/// could never reach.
///
/// This was `incomplete` and its name said so: at the widest width there is no wider
/// width to compute the exact product in, so the general path has no predicate to offer.
/// The constant path does not need the product -- `x * c` is inside the signed range
/// exactly when `x` is between `MAX / c` and `MIN / c` rounded one way or the other, and
/// both bounds are compile-time constants -- so it works here.
/// requires: a == 3
/// ensures: ret == 6
pub fn a_signed_constant_multiply_at_i64(a: i64) -> i64 {
    a * 2
}

/// The false direction of [`a_signed_constant_multiply_at_i64`], so the entry above is a
/// proof rather than a query the engine waved through.
/// requires: a == 3
/// ensures: ret == 7
pub fn a_signed_constant_multiply_at_i64_cannot_prove_this(a: i64) -> i64 {
    a * 2
}

/// A signed `i64` multiply by minus one at the one input it overflows on.
///
/// `-1 * i64::MIN` is `2^63`, one past `i64::MAX`. That is the case the first version of
/// the predicate called safe, by taking `-1` as never wrapping, so the entry is here to
/// keep the bound honest: the contract is *false* at `MIN`, and the tool must say so
/// rather than prove it.
/// requires: a == -9223372036854775808
/// ensures: ret == 0
pub fn a_signed_constant_multiply_by_minus_one_at_the_edge_cannot_prove_this(a: i64) -> i64 {
    a * -1
}

/// The unsigned multiply at `i64`'s width *is* decided, which is what makes the entry
/// above a width story rather than a sign story.
/// requires: a == 3
/// ensures: ret == 6
pub fn an_unsigned_constant_multiply_at_u64(a: u64) -> u64 {
    a * 2
}

/// A type whose method's tail collides with a *free function* of the same name.
///
/// The collision is deliberately on names used by nothing else in this file: a
/// shared tail is ambiguous everywhere it appears, so putting it on `set_lo` would
/// refuse every method call above rather than only the tripwire.
pub struct Widget {
    pub v: u8,
}

impl Widget {
    pub fn twist(&mut self, x: u8) {
        self.v = x;
    }
}

/// The free function that shares the tail `twist` with `Widget::twist`.
pub fn twist(v: &mut u8, x: u8) {
    *v = x;
}

/// The ambiguity tripwire: the call `w.twist(5)` names its receiver's type, so it
/// must resolve to `Widget::twist` and not to the free function `twist` that
/// shares the tail. The free function takes a different shape (`&mut u8`) and
/// would write through it, so inlining *it* would prove this false contract. The
/// resolver picks the method by the receiver's type, so the correct body runs and
/// the postcondition is refuted.
/// requires: w.v == 0
/// ensures: ret == 0
pub fn an_ambiguous_method_tail_cannot_prove_this(mut w: Widget) -> u8 {
    w.twist(5);
    w.v
}

/// The positional tripwire: the two fields are independent inputs, so a reader
/// that bound `p.0` and `p.1` to one variable would make `ret == p.0` hold --
/// with one variable, `max(v, v)` is `v`. With two, `p.0 <= p.1` and `p.0 != p.1`
/// gives `ret == p.1 != p.0`, so the contract is refuted. Refuted is the evidence
/// the fields are distinct rather than one aliased word.
/// requires: p.0 < p.1
/// ensures: ret == p.0
pub fn tuple_struct_fields_are_independent(p: &Pair) -> u8 {
    if p.0 > p.1 { p.0 } else { p.1 }
}

/// The index beyond the tuple's arity: `Pair` has two fields, so `p.2` names
/// nothing. It must be refused as an unknown field rather than bound to a
/// fabricated word.
/// requires: p.2 < 100
/// ensures: ret == 0
pub fn tuple_struct_out_of_range_field_is_refused(p: &Pair) -> u8 {
    let _ = p;
    0
}

/// A tuple struct whose single field is itself a struct: the projection is
/// nested, `n.p.0`. It is now *bound* -- `n.p` is a `Pair` with a readable layout
/// and `.0` is its first field -- so the contract is a real obligation rather than
/// a refusal. The body returns 0, so `ret == 0` verifies and the contract is
/// decided rather than skipped.
/// requires: n.p.0 < 100
/// ensures: ret == 0
pub fn nested_tuple_projection_reads(n: &NestedPair) -> u8 {
    let _ = n;
    0
}

/// The same nested path, but *read* by the body: the value the contract names as
/// `n.p.0` and the value the body reads are one input, so pinning it makes the
/// postcondition hold. A reader that bound the two separately would refute this.
/// requires: n.p.0 == 42
/// ensures: ret == 42
pub fn nested_tuple_projection_is_the_body_value(n: &NestedPair) -> u8 {
    n.p.0
}

/// The tripwire for the nested path: `n.p.0` and `n.p.1` are independent inputs,
/// so a reader that aliased them would prove `ret == n.p.0` vacuously. With two,
/// `n.p.0 < n.p.1` gives `ret == n.p.1 != n.p.0`, so the contract is refuted --
/// which is the evidence the two leaves are distinct.
/// requires: n.p.0 < n.p.1
/// ensures: ret == n.p.0
pub fn nested_tuple_projection_leaves_are_independent(n: &NestedPair) -> u8 {
    if n.p.0 > n.p.1 { n.p.0 } else { n.p.1 }
}

/// A nested path that walks off the layout: `n.p` is a `Pair` of scalars, so
/// `n.p.q` names a field `Pair` does not have. It must be refused as an unknown
/// field rather than bound to a fabricated word.
/// requires: n.p.q < 100
/// ensures: ret == 0
pub fn nested_path_off_the_layout_is_refused(n: &NestedPair) -> u8 {
    let _ = n;
    0
}

/// A *nested* field write through a `&mut`: `o.i.v = 5`.
///
/// MIR spells it `(((*_1).0).0: u8) = const 5_u8`, a walk of two field projections.
/// The single-field store is keyed by one field index, so a write there would land
/// on `(local, 0)` -- the *outer* field -- and the nested read would then see the
/// caller's value. This entry pins that the write lands where the read looks:
/// `ret == 5` holds only if `o.i.v` is the same input on both sides.
/// requires: true
/// ensures: ret == 5
pub fn nested_field_write_through_ref_mut_takes_effect(o: &mut OuterBox) -> u8 {
    o.i.v = 5;
    o.i.v
}

/// The false direction of [`nested_field_write_through_ref_mut_takes_effect`].
///
/// The body writes `5` and returns it, so `ret == 0` is false for every input. A
/// dropped or mis-keyed nested write would leave the read on the caller's
/// unconstrained leaf and make this *provable*; it must be refuted.
/// requires: true
/// ensures: ret == 0
pub fn nested_field_write_through_ref_mut_is_not_dropped(o: &mut OuterBox) -> u8 {
    o.i.v = 5;
    o.i.v
}

/// Overwriting the *whole* intermediate aggregate makes the seeded leaf stale.
///
/// `o.i = Inner { v: 9, .. }` replaces the value `o.i.v` was a part of, so the
/// seed for `o.i.v` no longer describes the store. The read must not return the
/// pre-write leaf: a reader that kept the stale seed would make this false contract
/// (`ret == 3`) *provable*. This entry pins the safe direction -- not verified.
/// requires: true
/// ensures: ret == 3
pub fn whole_inner_write_makes_nested_seed_stale(mut o: OuterBox) -> u8 {
    o.i = InnerBox { v: 9 };
    o.i.v
}

/// A whole-struct copy carries its *nested* parts, not only its single fields.
///
/// `c = d` copies the value, so `c.i.v` afterwards is `d.i.v`. Nested paths are
/// keyed by local, so a copy that moved only the single-field parts would leave
/// `c`'s own `c.i.v` seed in place and refute this true contract. The two
/// preconditions pin the two seeds to different values, so `verified` is the
/// evidence the copy moved the right one.
/// requires: c.i.v == 0
/// requires: d.i.v == 1
/// ensures: ret == 1
pub fn whole_struct_copy_carries_nested_paths(mut c: OuterBox, d: OuterBox) -> u8 {
    c = d;
    c.i.v
}

/// A *nested* aggregate literal lands where the read looks, and the false direction of
/// [`whole_inner_write_makes_nested_seed_stale`] is its tripwire.
///
/// `o.i = InnerBox { v: 9 }` lowers to a struct literal into a temp followed by
/// `(_1.0) = move _2`, so the parts being moved are keyed under `_2` and the destination
/// is the nested place `_1.0`. The copy that moves a *whole* local re-roots its parts; a
/// copy whose destination is itself nested did not, so the temp's `v` never landed under
/// `_1.0` and the later read `(_1.0).0` found nothing. The body then had no value, and
/// this true contract was `incomplete` rather than verified. `verified` here is the
/// positive evidence the re-rooting happened; the companion's refutation is the evidence
/// it happened in the direction the read consults.
/// requires: true
/// ensures: ret == 9
pub fn whole_inner_write_is_seen_by_the_leaf(mut o: OuterBox) -> u8 {
    o.i = InnerBox { v: 9 };
    o.i.v
}

/// The same nested aggregate literal, written *through a mutable reference*.
///
/// On an `&mut OuterBox` the assignment lowers to `((*_1).0) = move _2`, so the
/// destination's projection carries a leading deref. The re-rooting helper must strip that
/// deref -- as the nested *read* does, because an `&mut T` argument is modelled as its
/// referent -- or the write is refused for the wrong reason and the leaf reads `Unknown`.
/// `verified` here is the evidence the write reached the target's field path, and it is the
/// `&mut` companion to `whole_inner_write_is_seen_by_the_leaf`.
/// requires: true
/// ensures: ret == 9
pub fn whole_inner_write_through_a_mutable_reference_is_seen(o: &mut OuterBox) -> u8 {
    o.i = InnerBox { v: 9 };
    o.i.v
}

/// A nested-to-nested move, `o.i = o.j`.
///
/// The first step is the *nested source* `(_1.1)` moved into a whole temp, the second a whole
/// source into the nested destination `(_1.0)`. `copy_parts` refuses a nested source, so
/// without the re-rooting the leaf reads `Unknown`. The precondition pins `o.i.v` to `7`, which
/// the move overwrites with the source's `3` -- so the true `ret == 3` is the evidence the
/// *source's* leaf arrived.
/// requires: o.i.v == 7
/// ensures: ret == 3
pub fn whole_inner_move_carries_the_source_leaf(mut o: OuterBox) -> u8 {
    o.j.v = 3;
    o.i = o.j;
    o.i.v
}

/// The false twin of [`whole_inner_move_carries_the_source_leaf`].
///
/// Same body, but the contract claims the *destination's* pre-move leaf survived. A model
/// that kept `o.i.v`'s stale `7` instead of the source's `3` would prove this; it must be
/// refuted, and the witness is `o.i.v` at its seeded `7` (the value the move replaced).
/// requires: o.i.v == 7
/// ensures: ret == 7
pub fn whole_inner_move_is_not_the_stale_destination(mut o: OuterBox) -> u8 {
    o.j.v = 3;
    o.i = o.j;
    o.i.v
}

/// A nested swap through a temp, `let t = o.i; o.i = o.j; o.j = t`.
///
/// Two nested sources and two nested destinations, so it only works if the re-rooting runs
/// on a nested source as well as a nested destination: the guard is "either side nested", not
/// "destination nested". The precondition pins the two sides apart (`3` and `4`), so the
/// returned `4` proves the *other* side arrived rather than the one that was already there.
/// requires: o.i.v == 3
/// requires: o.j.v == 4
/// ensures: ret == 4
pub fn nested_swap_carries_the_other_side(mut o: OuterBox) -> u8 {
    let tmp = o.i;
    o.i = o.j;
    o.j = tmp;
    o.i.v
}

/// The false twin of [`nested_swap_carries_the_other_side`].
///
/// Same body, but the contract claims the pre-swap `o.i.v == 3` survived. A model that
/// dropped the nested-to-nested move -- keeping each side's own leaf -- would prove this; it
/// must be refuted, and the witness is the two seeds (`3` and `4`) that the swap exchanged.
/// requires: o.i.v == 3
/// requires: o.j.v == 4
/// ensures: ret == 3
pub fn nested_swap_is_not_the_stale_side(mut o: OuterBox) -> u8 {
    let tmp = o.i;
    o.i = o.j;
    o.j = tmp;
    o.i.v
}

/// Identity, so a nested aggregate can be handed to a helper and read back.
///
/// The helper's return is an aggregate the callee built field-by-field, so the merge has to
/// carry the *fields*, not only the tuple components; without that the caller's `id_inner(o.i).v`
/// reads `Unknown` while the contract is true of the body.
pub fn identity_inner_box(x: InnerBox) -> InnerBox {
    x
}

/// A nested aggregate handed to a helper by value, and the helper's return read back.
///
/// `id_inner(o.i)` lowers to `_3 = move (_1.0); _2 = id_inner(move _3)`, so the aggregate
/// argument is a *sub-place* whose parts have to be carried in, and the callee's `_0 = _1`
/// return has to carry its fields back. The precondition pins the leaf so the returned `9` is
/// the value that crossed, not a fresh variable.
/// requires: o.i.v == 9
/// ensures: ret == 9
pub fn nested_aggregate_argument_reaches_the_helper(mut o: OuterBox) -> u8 {
    identity_inner_box(o.i).v
}

/// The false twin of [`nested_aggregate_argument_reaches_the_helper`].
///
/// Same body, but the contract claims a different value survived. A merge that dropped the
/// returned field would leave the read `Unknown` (a lost proof); one that kept a *stale* field
/// would prove this. It must be refuted, with the seeded `9` as the witness.
/// requires: o.i.v == 9
/// ensures: ret == 7
pub fn nested_aggregate_argument_is_not_the_stale_destination(mut o: OuterBox) -> u8 {
    identity_inner_box(o.i).v
}

/// Build an `OuterBox` around an inner value, so a returned struct *field* can be read.
pub fn wrap_inner_box(x: InnerBox) -> OuterBox {
    OuterBox { i: x, j: InnerBox { v: 0 } }
}

/// A returned struct's *field* is read back through a two-level path.
///
/// `wrap_inner_box(o.i)` lowers to `_0 = OuterBox { i: copy _1, j: move _2 }`, so the returned
/// field's own parts have to be re-rooted onto `_0.i` -- the `Struct` literal stores the field
/// value but not the operand aggregate's `v`. The precondition pins the leaf so the returned
/// `9` is the value that crossed.
/// requires: o.i.v == 9
/// ensures: ret == 9
pub fn nested_return_carries_the_field(mut o: OuterBox) -> u8 {
    wrap_inner_box(o.i).i.v
}

/// The false twin of [`nested_return_carries_the_field`].
///
/// Same body, but the contract claims a different leaf survived. It must be refuted, with the
/// seeded `9` as the witness.
/// requires: o.i.v == 9
/// ensures: ret == 3
pub fn nested_return_is_not_the_stale_field(mut o: OuterBox) -> u8 {
    wrap_inner_box(o.i).i.v
}

/// The inner type of [`nested_tuple_projection_reads`].
pub struct NestedPair { pub p: Pair }

/// A *named-field* struct whose field is itself a named-field struct, so the
/// contract can name `o.i.v`. The read is bound to the body's value: pinning
/// `o.i.v` makes the postcondition hold, which a reader that bound the two
/// separately would refute.
/// requires: o.i.v == 7
/// ensures: ret == 7
pub fn nested_named_field_reads_its_leaf(o: &OuterBox) -> u8 {
    o.i.v
}

/// The named-field tripwire: `o.i.v` and `o.j.v` are leaves under *different*
/// outer fields, so a reader that keyed only on the leaf name would alias them and
/// prove `ret == o.j.v` vacuously. With distinct chains, `o.i.v != o.j.v` holds
/// and the contract is refuted -- the evidence the paths are distinct inputs.
/// requires: o.i.v != o.j.v
/// ensures: ret == o.j.v
pub fn nested_named_leaves_under_different_fields(o: &OuterBox) -> u8 {
    o.i.v
}

/// A nested named-field read that the *body* performs, so the contract's `o.i.v`
/// and the body's `(((*_1).0).0)` must be the same input for this to verify.
/// requires: o.i.v <= 200
/// ensures: ret == o.i.v
pub fn nested_named_field_is_the_body_value(o: &OuterBox) -> u8 {
    o.i.v
}

/// The named-field types for the nested named-field entries above.
pub struct InnerBox { pub v: u8 }
pub struct OuterBox { pub i: InnerBox, pub j: InnerBox }

/// A signed `i64` division by a constant power of two, which the divider's sign fixup
/// could not reach.
///
/// `a / 2` is a shift on a power-of-two divisor, so it needs neither the restoring
/// divider nor the sign fixup that made the general path a wall at this width.
/// requires: a == -7
/// ensures: ret == -3
pub fn a_signed_constant_division_at_i64(a: i64) -> i64 {
    a / 2
}

/// The false direction of [`a_signed_constant_division_at_i64`], so the entry is a proof
/// rather than a query the engine waved through.
/// requires: a == -7
/// ensures: ret == -4
pub fn a_signed_constant_division_at_i64_cannot_prove_this(a: i64) -> i64 {
    a / 2
}

/// A signed `i64` remainder by a constant power of two.
///
/// `-7 % 2` is `-1`: the remainder takes the *dividend's* sign, and the constant path
/// builds it as `x - q * 2^k` from the `|c|` quotient, so it needs no sign fixup either.
/// requires: a == -7
/// ensures: ret == -1
pub fn a_signed_constant_remainder_at_i64(a: i64) -> i64 {
    a % 2
}

/// A signed `i64` division by a *negative* constant power of two.
///
/// `-7 / -2` is `3` in Rust: truncation toward zero, so the sign of the result follows the
/// signs of the operands. The constant path negates the magnitude quotient for this case.
/// requires: a == -7
/// ensures: ret == 3
pub fn a_signed_constant_division_by_a_negative_power_of_two_at_i64(a: i64) -> i64 {
    a / -2
}

/// A signed `i64` division by a constant that is *not* a power of two.
///
/// `3` has no shift identity, so this stays on the general divider. It is the shape that
/// used to overflow the stack rather than report: the fold-built term is deep, and the walk
/// had no depth bound.
///
/// The precondition pins `a`, so the divider folds to a literal and the query is decided.
/// [`a_symbolic_division_by_a_non_power_of_two_at_i64`] is the same body *without* the pin,
/// which keeps the general divider built -- that one is the deep-walk vehicle.
/// requires: a == -7
/// ensures: ret == -2
pub fn a_signed_division_by_a_non_power_of_two_at_i64(a: i64) -> i64 {
    a / 3
}

/// The same general divider with a *symbolic* dividend, so the precondition does not pin
/// `a` and the constant folds cannot collapse the division.
///
/// This is the deepest legitimate term walk in the corpus: the 64-bit restoring divider is
/// a chain of adders and muxes ~262 terms deep, which no step budget sees. It is the shape
/// that aborted the process before `MAX_WALK_DEPTH`, and it is the vehicle for
/// `a_deep_term_walk_is_refused_not_allowed_to_overflow_the_stack`. The contract is false in
/// general (`a / 3 == -2` only for some `a`), so a decided verdict is a counterexample and an
/// undecided one is the refusal -- never `Verified`, and never a crash.
/// requires: true
/// ensures: ret == -2
pub fn a_symbolic_division_by_a_non_power_of_two_at_i64(a: i64) -> i64 {
    a / 3
}

/// A precondition can pin a *field* to a constant, not just an argument.
///
/// `requires: w.v == -7` fixes the only input the body reads, so `w.v / 3` folds to a
/// literal quotient exactly as the argument-level pin does. Before the pin was keyed by
/// the variable's index rather than the argument's local, this field stayed symbolic: the
/// 64-bit restoring divider was built in full and the query was refused for the size of
/// its own diagram (1.18s, `incomplete`) even though the precondition left one value.
/// [`a_field_pinned_division_cannot_prove_this`] is the false direction, so the entry
/// above is a proof and not a vacuous `true`.
pub struct WideBox {
    pub v: i64,
}

/// requires: w.v == -7
/// ensures: ret == -2
pub fn a_field_pinned_division_at_i64(w: WideBox) -> i64 {
    w.v / 3
}

/// The same field pin with a claim the fold refutes, so the entry above cannot pass by
/// being decided to `true` for the wrong reason.
/// requires: w.v == -7
/// ensures: ret == 99
pub fn a_field_pinned_division_cannot_prove_this(w: WideBox) -> i64 {
    w.v / 3
}

/// A pin on a *nested* path (`o.i.v`) folds the body that reads it, for the same reason:
/// the variable the contract names is the one the body's projection reads. The fields are
/// `i64` so the general divider is the expensive shape the pin has to close.
pub struct WideInner {
    pub v: i64,
}

pub struct WideOuter {
    pub i: WideInner,
}

/// requires: o.i.v == -7
/// ensures: ret == -2
pub fn a_nested_pinned_division_at_i64(o: WideOuter) -> i64 {
    o.i.v / 3
}

/// The false direction of the nested pin.
/// requires: o.i.v == -7
/// ensures: ret == 99
pub fn a_nested_pinned_division_cannot_prove_this(o: WideOuter) -> i64 {
    o.i.v / 3
}

/// A pin reaches an *element* of an array, not just a field. `requires: xs[0] == -7` names
/// an element, and the body reads the same element, so the divider folds.
/// requires: xs[0] == -7
/// ensures: ret == -2
pub fn an_element_pinned_division_at_i64(xs: [i64; 2]) -> i64 {
    xs[0] / 3
}

/// The false direction of the element pin.
/// requires: xs[0] == -7
/// ensures: ret == 99
pub fn an_element_pinned_division_cannot_prove_this(xs: [i64; 2]) -> i64 {
    xs[0] / 3
}

/// A pin whose right-hand side names an *earlier* pinned variable, so the chain has to be
/// followed before the body folds.
///
/// `b == a + 1` does not evaluate until `a`'s pin exists, so a single-pass extraction
/// pinned only `a` and left `b` symbolic -- and a symbolic operand builds the full circuit
/// whatever the other operand is. The three links here (`a`, then `b` through an add, then
/// `c` through a multiply) are the shape the fixpoint exists for, and the multiply is
/// deliberate: the *pin* makes the body's dividend a literal, but the path condition still
/// carries `c == b * 2` at 64 bits, which is the diagram the goal check has to get past.
///
/// [`a_transitive_pin_chain_cannot_prove_this`] is the false direction, so the entry above
/// is a proof rather than a `true` that a broken extraction would also produce.
/// requires: a == 5 && b == a + 1 && c == b * 2
/// ensures: ret == 3
pub fn a_transitive_pin_chain_folds_the_body(a: i64, b: i64, c: i64) -> i64 {
    let _ = (a, b);
    c / 4
}

/// The false direction of the transitive chain: the pin fixes `c` at `12`, so the claim is
/// refuted by the fold rather than proved.
/// requires: a == 5 && b == a + 1 && c == b * 2
/// ensures: ret == 99
pub fn a_transitive_pin_chain_cannot_prove_this(a: i64, b: i64, c: i64) -> i64 {
    let _ = (a, b);
    c / 4
}


/// An *unsigned* division by a power of two, with a symbolic dividend.
///
/// The signed twin of this shape was already a shift, but the unsigned side fell through
/// to the general restoring divider -- a term ~`2 * w` deep -- and a symbolic dividend
/// through it was refused for the diagram's size: `incomplete` in ~0.9 s at `u64`. The
/// quotient of an unsigned value by `2^k` is the logical shift `n >> k`, so the body folds
/// to a handful of terms and the bound decides it.
///
/// [`an_unsigned_power_of_two_division_cannot_prove_this`] is the false direction, so the
/// entry above is a proof and not a `true` that a too-permissive fast path would also
/// produce.
/// requires: n >= 4 && n <= 7
/// ensures: ret == 1
pub fn an_unsigned_power_of_two_division_is_decided(n: u64) -> u64 {
    n / 4
}

/// The false direction of the unsigned shift identity: `n` in `[4, 7]` makes `n / 4` one,
/// so the claim of two is refuted.
/// requires: n >= 4 && n <= 7
/// ensures: ret == 2
pub fn an_unsigned_power_of_two_division_cannot_prove_this(n: u64) -> u64 {
    n / 4
}

/// An *unsigned* remainder by a power of two, which is a mask rather than a divider.
///
/// The companion to the division above, and it exercises the other half of
/// `udivmod_pow2`: `n % 4 == n & 3`. The general divider would be built for a mask.
/// requires: n >= 4 && n <= 7
/// ensures: ret <= 3
pub fn an_unsigned_power_of_two_remainder_is_decided(n: u64) -> u64 {
    n % 4
}


/// An element of an array reached through a struct field, written and read back.
///
/// `x.a[0] = 9; x.a[0]` lowers to `(_1.0)[_2] = const 9_u8` and `_0 = copy (_1.0)[_4]`: the
/// store is keyed by the whole path (the local, the field chain to the array, the index),
/// so `x.a[0]` and `x.b[0]` are different words and the write is visible to the read. Before
/// this the write was dropped and the read returned the *seed*, which is the false-proof
/// direction: a contract claiming the pre-write value would have been proved.
///
/// [`a_field_array_write_is_not_the_seed`] is the false direction, so the entry above is a
/// proof and not a `true` that a broken store would also produce.
/// requires: x.a[0] == 5
/// ensures: ret == 9
pub fn a_field_array_write_is_read_back(mut x: Boxed) -> u8 {
    x.a[0] = 9;
    x.a[0]
}

/// The false direction of the field-array write: the body stores 9, so a claim of the seed
/// is refuted rather than proved.
/// requires: x.a[0] == 5
/// ensures: ret == 5
pub fn a_field_array_write_is_not_the_seed(mut x: Boxed) -> u8 {
    x.a[0] = 9;
    x.a[0]
}

/// Writing one field's array element leaves the sibling array's element alone.
///
/// The whole path is the key, so `x.a[0] = 9` must not disturb `x.b[0]`. A store keyed by
/// the local and index alone would collide the two and prove `ret == 7` against the wrong
/// element.
/// requires: x.b[0] == 7
/// ensures: ret == 7
pub fn a_sibling_field_array_is_untouched(mut x: Boxed) -> u8 {
    x.a[0] = 9;
    x.b[0]
}

/// A struct with two arrays, so a contract can name both fields' elements.
pub struct Boxed {
    pub a: [u8; 4],
    pub b: [u8; 4],
}

/// An array element reached through a *nested* field path is the same word on both sides.
///
/// `o.i.a[0] = 9; o.i.a[0]` lowers to `(_1.0.0)[_2] = 9` and `_0 = copy (_1.0.0)[_4]`. The
/// element's key is the *whole* field chain, so a nested array is not mistaken for the
/// first-level `o.i`; the store and the contract agree on the deeper path.
///
/// [`a_nested_field_array_write_is_not_the_seed`] is the false direction.
/// requires: o.i.a[0] == 5
/// ensures: ret == 9
pub fn a_nested_field_array_write_is_read_back(mut o: NestedArrays) -> u8 {
    o.i.a[0] = 9;
    o.i.a[0]
}

/// The false direction of the nested field-array write: the body stores 9, so a claim of
/// the seed is refuted rather than proved.
/// requires: o.i.a[0] == 5
/// ensures: ret == 5
pub fn a_nested_field_array_write_is_not_the_seed(mut o: NestedArrays) -> u8 {
    o.i.a[0] = 9;
    o.i.a[0]
}

/// A struct whose array lives one aggregate down, so the contract's path is `o.i.a[0]`.
pub struct NestedArrays {
    pub i: ArrayHolder,
    pub k: u8,
}

/// The inner aggregate holding the array.
pub struct ArrayHolder {
    pub a: [u8; 4],
}

/// A helper's write to a *field-array element* through `&mut` must cross back to the caller.
///
/// `set_first(x); x.a[0]` calls `set_first(&mut Boxed)` which stores `x.a[0] = 9`. The
/// callee's write lands in `elems_path` under its own local, so the caller's store has to be
/// re-based on return -- without that the write died with the frame and the caller read its
/// *seed*, proving the false `ret == 5` against a body returning 9.
///
/// [`a_helper_field_array_write_is_not_the_seed`] is the false direction.
/// requires: x.a[0] == 5
/// ensures: ret == 9
pub fn a_helper_field_array_write_is_read_back(x: &mut Boxed) -> u8 {
    set_first_element(x);
    x.a[0]
}

/// The false direction of the helper field-array write: the helper stores 9, so a claim of
/// the caller's seed is refuted rather than proved.
/// requires: x.a[0] == 5
/// ensures: ret == 5
pub fn a_helper_field_array_write_is_not_the_seed(x: &mut Boxed) -> u8 {
    set_first_element(x);
    x.a[0]
}

/// The helper that writes one field-array element through its `&mut` argument.
fn set_first_element(x: &mut Boxed) {
    x.a[0] = 9;
}

/// A helper handed a *nested aggregate* (`&mut o.i`) that writes an element of the array
/// inside it: the callee's `_1.a[0]` is the caller's `o.i.a[0]`, so the write-back has to
/// prefix the target's chain. The sibling `o.k` is left alone.
///
/// [`a_helper_nested_aggregate_element_write_is_not_the_seed`] is the false direction.
/// requires: o.i.a[0] == 5
/// ensures: ret == 9
pub fn a_helper_nested_aggregate_element_write_is_read_back(mut o: NestedArrays) -> u8 {
    set_holder_first_element(&mut o.i);
    o.i.a[0]
}

/// The false direction of the nested-aggregate element write: the helper stores 9, so a
/// claim of the seed is refuted rather than proved.
/// requires: o.i.a[0] == 5
/// ensures: ret == 5
pub fn a_helper_nested_aggregate_element_write_is_not_the_seed(mut o: NestedArrays) -> u8 {
    set_holder_first_element(&mut o.i);
    o.i.a[0]
}

/// A helper handed a *shared* nested aggregate that only *reads* the array element: the
/// caller's seed has to cross *into* the callee, or the callee's read is unknown and the
/// true contract is unreadable rather than decided.
/// requires: o.i.a[0] == 5
/// ensures: ret == 5
pub fn a_helper_nested_aggregate_element_read(mut o: NestedArrays) -> u8 {
    read_holder_first_element(&o.i)
}

/// The reading helper: its argument is a `&ArrayHolder`, and `i.a[0]` is the caller's
/// `o.i.a[0]`.
fn read_holder_first_element(i: &ArrayHolder) -> u8 {
    i.a[0]
}

/// The writing helper for a nested aggregate target: `i.a[0]` is the caller's `o.i.a[0]`.
fn set_holder_first_element(i: &mut ArrayHolder) {
    i.a[0] = 9;
}

/// The whole-array-target case: an array handed over *as* a reference target
/// (`&mut x.a`) crosses the frame.
///
/// `set_first_of(&mut x.a)` passes a `&mut [u8; 4]` whose target is the *field* `x.a`,
/// not the whole local. The callee's `(*_1)[0] = 9` lands in the callee's own element
/// store, and the return path re-bases it onto the caller's field-path element store
/// (`elems_path`, keyed by the field chain `x.a`) -- the key the caller's `x.a[0]` read
/// consults. So the write crosses the frame and the contract decides: `ret == 9`
/// verifies.
///
/// The false twin below is the other half, and it is what makes the decision
/// trustworthy: a re-basing that connected the two stores the *wrong* way would turn
/// the twin `Verified` before it turned this one verified. It does not -- the twin is
/// refuted -- so no false proof is claimed. The whole-*local* form
/// (`set_arr(&mut a); a[0]`) also decides, because the target has no projection and the
/// store is keyed by the local alone.
/// requires: x.a[0] == 5
/// ensures: ret == 9
pub fn a_whole_array_target_crosses_a_reference_argument(mut x: Boxed) -> u8 {
    set_first_of(&mut x.a);
    x.a[0]
}

/// The false direction of the whole-array target, named so the corpus-wide
/// `no_cannot_prove_entry_is_ever_verified` invariant holds it as well: it must never
/// become `Verified`.
/// requires: x.a[0] == 5
/// ensures: ret == 5
pub fn a_whole_array_target_cannot_prove_this(mut x: Boxed) -> u8 {
    set_first_of(&mut x.a);
    x.a[0]
}

/// The helper handed the *array itself* (`&mut [u8; 4]`) rather than the local that
/// holds it.
fn set_first_of(a: &mut [u8; 4]) {
    a[0] = 9;
}

/// The read-only half of the whole-array-target case: `&x.a` crosses the frame the same
/// way `&mut x.a` does.
///
/// `peek_of(&x.a)` hands the callee the array `x.a` as a `&[u8; 4]`, so the callee's
/// `a[0]` is the caller's `x.a[0]`. The carry-in re-bases the caller's field-path element
/// onto the callee's whole-local element store, so the read finds the seed and the
/// contract decides: `ret == 5` verifies. Without it the callee read `Unknown` and this
/// was `Incomplete` -- the exact mirror of the write direction above.
/// requires: x.a[0] == 5
/// ensures: ret == 5
pub fn a_whole_array_target_read_crosses_a_reference_argument(x: Boxed) -> u8 {
    peek_of(&x.a)
}

/// The false direction of the read-only whole-array target: the seed is 5, not 7.
/// requires: x.a[0] == 5
/// ensures: ret == 7
pub fn a_whole_array_target_read_cannot_prove_this(x: Boxed) -> u8 {
    peek_of(&x.a)
}

/// The reading helper for a whole-array target: its argument is the array `x.a` itself.
fn peek_of(a: &[u8; 4]) -> u8 {
    a[0]
}

/// The sibling-field direction of the whole-array target: the write to `x.a` must not
/// leak into `x.b`.
///
/// `set_first_of(&mut x.a)` writes `x.a[0]`, so `x.b[0]` is still the seed. Claiming
/// `ret == 9` here is false of the body and must be refuted; a re-basing that keyed the
/// callee's element on the local alone -- the field chain dropped -- would land the
/// write on whichever field the caller happened to read and *prove* this. The suffix
/// also puts it under the corpus-wide `no_cannot_prove_entry_is_ever_verified`
/// invariant.
/// requires: x.b[0] == 5
/// ensures: ret == 9
pub fn a_whole_array_target_sibling_cannot_prove_this(mut x: Boxed) -> u8 {
    set_first_of(&mut x.a);
    x.b[0]
}

/// A read-modify-write through a whole-array target: the callee *reads* the element it
/// also writes.
///
/// `bump_first_of(&mut x.a)` computes `x.a[0] + 1`, so this exercises both directions at
/// once -- the carry-in must hand the callee the caller's seed (else `a[0]` reads
/// `Unknown` and the add is an unmodelled operand) and the write-back must land the
/// result on the caller's `x.a[0]` (else the caller reads its own seed and `ret == 6`
/// is unprovable). Both are the same re-basing arm, so a fix that did only one would
/// fail here.
/// requires: x.a[0] == 5
/// ensures: ret == 6
pub fn a_whole_array_target_read_modify_write(mut x: Boxed) -> u8 {
    bump_first_of(&mut x.a);
    x.a[0]
}

/// The false direction of [`a_whole_array_target_read_modify_write`]: the seed, not the
/// incremented value. The suffix puts it under the corpus-wide
/// `no_cannot_prove_entry_is_ever_verified` invariant.
/// requires: x.a[0] == 5
/// ensures: ret == 5
pub fn a_whole_array_target_read_modify_write_cannot_prove_this(mut x: Boxed) -> u8 {
    bump_first_of(&mut x.a);
    x.a[0]
}

/// A whole-array target reached through a *nested* field path: `&mut o.i.a`.
///
/// The target's chain is two fields (`[0, 0]`), so the re-basing has to carry a chain of
/// more than one step, not just a single field. The helper is the same `set_first_of`, so
/// the difference from the flat case is the target's depth alone.
/// requires: o.i.a[0] == 5
/// ensures: ret == 9
pub fn a_nested_whole_array_target_crosses_a_reference_argument(mut o: NestedArrays) -> u8 {
    set_first_of(&mut o.i.a);
    o.i.a[0]
}

/// The false direction of [`a_nested_whole_array_target_crosses_a_reference_argument`].
/// requires: o.i.a[0] == 5
/// ensures: ret == 5
pub fn a_nested_whole_array_target_cannot_prove_this(mut o: NestedArrays) -> u8 {
    set_first_of(&mut o.i.a);
    o.i.a[0]
}

/// The write crosses *two* frames: the caller hands `&mut x.a` to a helper that hands the
/// same reference on to [`set_first_of`].
///
/// `relay_first_of` only forwards its argument, so the write reaches the caller's
/// `x.a[0]` through an inner call. Each frame re-bases independently, so this is the
/// transitivity check on the re-basing rule rather than a new rule.
/// requires: x.a[0] == 5
/// ensures: ret == 9
pub fn a_whole_array_target_crosses_two_frames(mut x: Boxed) -> u8 {
    relay_first_of(&mut x.a);
    x.a[0]
}

/// The false direction of [`a_whole_array_target_crosses_two_frames`].
/// requires: x.a[0] == 5
/// ensures: ret == 5
pub fn a_whole_array_target_crosses_two_frames_cannot_prove_this(mut x: Boxed) -> u8 {
    relay_first_of(&mut x.a);
    x.a[0]
}

/// A read-modify-write helper for a whole-array target: reads and writes element 0.
fn bump_first_of(a: &mut [u8; 4]) {
    a[0] = a[0] + 1;
}

/// A pass-through helper: forwards its whole-array reference to [`set_first_of`], so the
/// write crosses two frames.
fn relay_first_of(a: &mut [u8; 4]) {
    set_first_of(a);
}

impl Boxed {
    /// `&mut self.a[0]` -- the returned reference names an *element*, and the index the
    /// dump prints is a local (`_2`), not the literal.
    fn first_mut(&mut self) -> &mut u8 {
        &mut self.a[0]
    }

    /// `&mut self.a[1]` -- a second element, so a fix that pinned every returned element
    /// to index 0 would decide the first case and read the wrong element here.
    fn second_mut(&mut self) -> &mut u8 {
        &mut self.a[1]
    }
}

/// A method that returns `&mut` to an *element* of a field array: the write through the
/// returned reference must land on `x.a[0]`.
///
/// `x.first_mut()` builds `&mut x.a[0]` from `_1.0[_2]`, where `_2` is the local that held
/// `0`. The caller's place for the returned reference has to keep that element index, and
/// `_2` means nothing outside the callee -- so a translation that carried the local through
/// left a place no element store is keyed by, the write was dropped, and the contract was
/// unreadable. Pinning the index to its literal while the callee's locals are still live is
/// what makes `ret == 9` decide; a symbolic index is left alone, so no write lands on an
/// element the caller never named.
/// requires: x.a[0] == 5
/// ensures: ret == 9
pub fn returned_ref_to_an_element_crosses_the_frame(mut x: Boxed) -> u8 {
    *x.first_mut() = 9;
    x.a[0]
}

/// The false direction of [`returned_ref_to_an_element_crosses_the_frame`]: the seed, not
/// the write. A re-basing that aimed the write at the wrong element could turn this twin
/// `Verified` before the true case, so it is held by the corpus-wide
/// `no_cannot_prove_entry_is_ever_verified` invariant.
/// requires: x.a[0] == 5
/// ensures: ret == 5
pub fn returned_ref_to_an_element_cannot_prove_this(mut x: Boxed) -> u8 {
    *x.first_mut() = 9;
    x.a[0]
}

/// The second element: a fix that pinned every returned element to index 0 would decide the
/// case above and read the wrong element here.
/// requires: x.a[1] == 5
/// ensures: ret == 9
pub fn returned_ref_to_a_sibling_element(mut x: Boxed) -> u8 {
    *x.second_mut() = 9;
    x.a[1]
}

/// The false direction of [`returned_ref_to_a_sibling_element`].
/// requires: x.a[1] == 5
/// ensures: ret == 5
pub fn returned_ref_to_a_sibling_element_cannot_prove_this(mut x: Boxed) -> u8 {
    *x.second_mut() = 9;
    x.a[1]
}

/// The write through the returned reference must not land on a *different* element.
///
/// The method writes `x.a[1]`, so `x.a[0]` is still the seed. Claiming `ret == 9` here is
/// false of the body; an element index that was dropped or defaulted would prove it.
/// requires: x.a[0] == 5
/// ensures: ret == 9
pub fn returned_ref_write_is_not_the_wrong_element_cannot_prove_this(mut x: Boxed) -> u8 {
    *x.second_mut() = 9;
    x.a[0]
}

/// A helper that returns `&mut` to an element of the array it was handed: the write
/// through the returned reference must reach the caller's array.
///
/// `elem_mut(&mut x.a)` passes the array `x.a` *itself*; inside, `&mut a[0]` is
/// `(*_1)[_2]` -- a deref of the reference argument followed by the element index. The
/// translation back to the caller appended that projection to `x.a`, leaving a deref in
/// the middle of the caller's place where no element store is keyed. The write was
/// dropped, the caller read its own seed, and the *false* direction below was **proved**
/// against a body returning 9 -- a false proof, not a lost one. Stripping the argument's
/// deref (the head `arg_source` already names) and pinning the index is what makes the
/// true contract decide and the false twin refute.
/// requires: x.a[0] == 5
/// ensures: ret == 9
pub fn returned_ref_to_a_whole_array_element(mut x: Boxed) -> u8 {
    let r = elem_mut(&mut x.a);
    *r = 9;
    x.a[0]
}

/// The false direction of [`returned_ref_to_a_whole_array_element`]: the seed, not the
/// write. This is the entry the pre-fix engine *proved*, so it is the sharpest tooth here.
/// requires: x.a[0] == 5
/// ensures: ret == 5
pub fn returned_ref_to_a_whole_array_element_cannot_prove_this(mut x: Boxed) -> u8 {
    let r = elem_mut(&mut x.a);
    *r = 9;
    x.a[0]
}

/// The reading helper for [`returned_ref_to_a_whole_array_element`]: returns `&mut` to
/// element 0 of the array it is handed.
fn elem_mut(a: &mut [u8; 4]) -> &mut u8 {
    &mut a[0]
}

/// A returned reference to an element reached through a *nested* field path: the origin is
/// `(*_1).i.a[_2]`, so the appended projection is a chain of two fields and an index.
/// requires: o.i.a[0] == 5
/// ensures: ret == 9
pub fn returned_ref_to_a_nested_whole_array_element(mut o: NestedArrays) -> u8 {
    *deep_elem_mut(&mut o) = 9;
    o.i.a[0]
}

/// The false direction of [`returned_ref_to_a_nested_whole_array_element`].
/// requires: o.i.a[0] == 5
/// ensures: ret == 5
pub fn returned_ref_to_a_nested_whole_array_element_cannot_prove_this(mut o: NestedArrays) -> u8 {
    *deep_elem_mut(&mut o) = 9;
    o.i.a[0]
}

/// The nested reading helper: `&mut o.i.a[0]`.
fn deep_elem_mut(o: &mut NestedArrays) -> &mut u8 {
    &mut o.i.a[0]
}

/// A returned reference to a *guarded* symbolic element: `x.nth_mut(i)` is `&mut x.a[i]`
/// and the contract admits only `i == 0`, so the write lands on `x.a[0]` and `ret == 9`
/// decides. The guard is what makes the symbolic index a single element.
/// requires: x.a[0] == 5 && i == 0
/// ensures: ret == 9
pub fn returned_ref_to_a_guarded_symbolic_element(mut x: Boxed, i: usize) -> u8 {
    *x.nth_mut(i) = 9;
    x.a[0]
}

/// The false direction of [`returned_ref_to_a_guarded_symbolic_element`]: same body, so
/// claiming the seed must be refuted.
/// requires: x.a[0] == 5 && i == 0
/// ensures: ret == 5
pub fn returned_ref_to_a_guarded_symbolic_element_cannot_prove_this(mut x: Boxed, i: usize) -> u8 {
    *x.nth_mut(i) = 9;
    x.a[0]
}

/// A returned reference to an element under a *symbolic* index the contract does not pin:
/// `i` may be any of the four elements, so the write cannot be aimed at `x.a[0]`. The
/// engine must not prove either direction -- the true `ret == 9` is a refusal, and the
/// false `ret == 5` must not be a false proof.
/// requires: x.a[0] == 5
/// ensures: ret == 5
pub fn returned_ref_to_an_unpinned_symbolic_element_cannot_prove_this(mut x: Boxed, i: usize) -> u8 {
    *x.nth_mut(i) = 9;
    x.a[0]
}

/// A returned reference to an element under a symbolic index, with the caller's
/// numbering *shifted* by an extra parameter so the callee's index local number
/// names a different caller local.
///
/// Inside `nth_mut` the index is `_2`, but `_2` in this caller is `zero`, not `i`.
/// Carried across the call boundary, the write `*x.nth_mut(i) = 9` landed on
/// `x.a[zero]` -- and the contract fixes `zero == 0`, so it landed on the *seed*
/// element `x.a[0]` and the false `ret == 5` was **proved**. The index cannot be
/// pinned (the contract admits any `i < 4`), so the write may hit any element and
/// must be refused, never aimed at a caller local that happens to share its number.
/// requires: x.a[0] == 5 && zero == 0 && i < 4
/// ensures: ret == 5
pub fn a_shifted_symbolic_element_cannot_prove_this(mut x: Boxed, zero: usize, i: usize) -> u8 {
    *x.nth_mut(i) = 9;
    x.a[0]
}

/// The true direction of [`a_shifted_symbolic_element_cannot_prove_this`]: the
/// write may land on any element, so `ret == 9` is a refusal, not a proof. A fix
/// that dropped the write and left the seed readable would turn the false
/// direction above around and prove *this* one instead, so both are pinned.
/// requires: x.a[0] == 5 && zero == 0 && i < 4
/// ensures: ret == 9
pub fn a_shifted_symbolic_element_is_not_proved(mut x: Boxed, zero: usize, i: usize) -> u8 {
    *x.nth_mut(i) = 9;
    x.a[0]
}

/// `&mut self.a[i]` -- a method whose returned reference names an element under a symbolic
/// index.
impl Boxed {
    fn nth_mut(&mut self, i: usize) -> &mut u8 {
        &mut self.a[i]
    }
}

/// A struct literal's array field carries its elements.
///
/// `ArrayHolder { a: [9, 1, 2, 3] }` builds the array in a temp whose elements live in
/// `elems`, then moves it into the field `_2.0`. The move carried the field's *value* but
/// not its elements -- `rebase_parts` re-based `elems_path` (field-path arrays) and missed
/// the whole-local `elems` store -- so `x.a[0]` read `Unknown` and the contract stayed
/// `Incomplete` in *both* directions. That is a coverage hole, not a false proof: a
/// missing value proves nothing, so the true `ret == 9` was merely lost. A bare array
/// literal (`let a = [9, 1, 2, 3]; a[0]`) always worked, which is why only the field case
/// showed the hole.
/// requires: true
/// ensures: ret == 9
pub fn a_struct_literal_array_element_is_read_back() -> u8 {
    let x = ArrayHolder { a: [9, 1, 2, 3] };
    x.a[0]
}

/// The false direction of [`a_struct_literal_array_element_is_read_back`]: a carry that
/// landed every element on index 0, or dropped the indices, would decide the wrong one.
/// requires: true
/// ensures: ret == 1
pub fn a_struct_literal_array_element_is_not_the_seed_cannot_prove_this() -> u8 {
    let x = ArrayHolder { a: [9, 1, 2, 3] };
    x.a[0]
}

/// The element at a *different* index, so a fix that pinned the first element for all of
/// them is caught.
/// requires: true
/// ensures: ret == 1
pub fn a_struct_literal_array_second_element_is_read_back() -> u8 {
    let x = ArrayHolder { a: [9, 1, 2, 3] };
    x.a[1]
}

/// The false direction of [`a_struct_literal_array_second_element_is_read_back`].
/// requires: true
/// ensures: ret == 9
pub fn a_struct_literal_array_second_element_is_not_the_first_cannot_prove_this() -> u8 {
    let x = ArrayHolder { a: [9, 1, 2, 3] };
    x.a[1]
}

/// A *nested* struct literal: the array field is one level deeper, so the move re-roots the
/// elements under a longer destination chain.
/// requires: true
/// ensures: ret == 9
pub fn a_nested_struct_literal_array_element_is_read_back() -> u8 {
    let o = NestedArrays { i: ArrayHolder { a: [9, 1, 2, 3] }, k: 0 };
    o.i.a[0]
}

/// The false direction of [`a_nested_struct_literal_array_element_is_read_back`].
/// requires: true
/// ensures: ret == 1
pub fn a_nested_struct_literal_array_element_is_not_the_seed_cannot_prove_this() -> u8 {
    let o = NestedArrays { i: ArrayHolder { a: [9, 1, 2, 3] }, k: 0 };
    o.i.a[0]
}

/// A whole-field assignment through a reference carries the array field's elements to the
/// caller. The callee's `*h = n` replaces the field, and the elements of the moved array
/// have to reach the caller's store or `o.i.a[0]` reads its seed.
/// requires: o.i.a[0] == 7
/// ensures: ret == 9
pub fn a_whole_field_assignment_carries_its_array_elements(mut o: NestedArrays) -> u8 {
    set_holder(&mut o.i, ArrayHolder { a: [9, 1, 2, 3] });
    o.i.a[0]
}

/// The false direction of [`a_whole_field_assignment_carries_its_array_elements`].
/// requires: o.i.a[0] == 7
/// ensures: ret == 7
pub fn a_stale_whole_field_array_element_cannot_prove_this(mut o: NestedArrays) -> u8 {
    set_holder(&mut o.i, ArrayHolder { a: [9, 1, 2, 3] });
    o.i.a[0]
}

/// The whole-field replacement must not disturb a sibling scalar.
/// requires: o.k == 5
/// ensures: ret == 5
pub fn a_whole_field_assignment_leaves_its_sibling(mut o: NestedArrays) -> u8 {
    set_holder(&mut o.i, ArrayHolder { a: [9, 1, 2, 3] });
    o.k
}

/// The false direction of [`a_whole_field_assignment_leaves_its_sibling`]: a re-base that
/// spilled the moved elements onto the sibling would decide this.
/// requires: o.k == 5
/// ensures: ret == 9
pub fn a_whole_field_assignment_leaves_its_sibling_cannot_prove_this(mut o: NestedArrays) -> u8 {
    set_holder(&mut o.i, ArrayHolder { a: [9, 1, 2, 3] });
    o.k
}

/// An array *field* read through a reference argument: the referent's elements are carried
/// in, so the callee's `h.a[0]` reads the caller's element.
/// requires: h.a[0] == 5
/// ensures: ret == 5
pub fn an_array_field_argument_is_read_by_element(h: ArrayHolder) -> u8 {
    h.a[0]
}

/// The false direction of [`an_array_field_argument_is_read_by_element`].
/// requires: h.a[0] == 5
/// ensures: ret == 9
pub fn an_array_field_argument_is_read_by_element_cannot_prove_this(h: ArrayHolder) -> u8 {
    h.a[0]
}

/// A helper replacing a whole `ArrayHolder` through a reference.
pub fn set_holder(h: &mut ArrayHolder, n: ArrayHolder) {
    *h = n;
}

/// A whole-aggregate replacement through a sub-place target decides.
///
/// `set_whole(&mut o.i, InnerBox { v: 9 })` replaces the whole referent, and the moved value's
/// leaf must reach the caller. This was once believed *sound-incomplete*; it is not -- the
/// re-based write-back re-roots the callee's `fields` entry under the target's chain, and a
/// whole value and a leaf write are both a `fields` entry there.
/// requires: o.i.v == 7
/// ensures: ret == 9
pub fn whole_replacement_through_sub_place(mut o: OuterBox) -> u8 {
    set_whole(&mut o.i, InnerBox { v: 9 });
    o.i.v
}

/// The false direction of [`whole_replacement_through_sub_place`]: a dropped replacement
/// would leave the seed, so this would verify.
/// requires: o.i.v == 7
/// ensures: ret == 7
pub fn whole_replacement_through_sub_place_cannot_prove_this(mut o: OuterBox) -> u8 {
    set_whole(&mut o.i, InnerBox { v: 9 });
    o.i.v
}

/// The replacement must not spill onto the sibling field.
/// requires: o.j.v == 5
/// ensures: ret == 5
pub fn whole_replacement_leaves_the_sibling(mut o: OuterBox) -> u8 {
    set_whole(&mut o.i, InnerBox { v: 9 });
    o.j.v
}

/// The false direction of [`whole_replacement_leaves_the_sibling`]: a write-back that
/// re-rooted onto the whole local instead of the target's chain would prove this.
/// requires: o.j.v == 5
/// ensures: ret == 9
pub fn whole_replacement_leaves_the_sibling_cannot_prove_this(mut o: OuterBox) -> u8 {
    set_whole(&mut o.i, InnerBox { v: 9 });
    o.j.v
}

/// A replacement whose value is built in a caller local, so the carry crosses the frame
/// from a temp rather than a literal.
/// requires: o.i.v == 7
/// ensures: ret == 9
pub fn whole_replacement_from_a_local(mut o: OuterBox) -> u8 {
    let n = InnerBox { v: 9 };
    set_whole(&mut o.i, n);
    o.i.v
}

/// The false direction of [`whole_replacement_from_a_local`].
/// requires: o.i.v == 7
/// ensures: ret == 7
pub fn whole_replacement_from_a_local_cannot_prove_this(mut o: OuterBox) -> u8 {
    let n = InnerBox { v: 9 };
    set_whole(&mut o.i, n);
    o.i.v
}

/// A helper replacing a whole aggregate through a reference.
pub fn set_whole(i: &mut InnerBox, n: InnerBox) {
    *i = n;
}

// ---------------------------------------------------------------------------
// Named `const` items
//
// rustc const-evaluates a `const` item and prints its body separately
// (`const LIMIT: u8 = const 10_u8;`), referring to it by name at the use site
// (`_0 = const LIMIT`). Without inlining the definition the use site is an
// unreadable path constant and the contract is lost -- not wrongly proved, but
// never decided. These pin the shapes that inlining must decide, each with its
// false twin so a future regression that *guessed* a value would be caught.
// ---------------------------------------------------------------------------

/// A limit constant, the shape a bounds check reads.
const LIMIT: u8 = 10;

/// A wider constant, so the width comes from the item's own suffix.
const WIDE_LIMIT: u16 = 1000;

/// A constant whose definition is another constant; rustc prints the *evaluated*
/// value, so `const NEXT: u8 = const 11_u8;`.
const NEXT: u8 = LIMIT + 1;

/// A negative constant, whose sign must survive inlining.
const NEG: i8 = -1;

/// A boolean constant.
const ENABLED: bool = true;

/// Reading a named constant decides.
/// requires: true
/// ensures: ret == 10
pub fn named_const_is_read(x: u8) -> u8 {
    let _ = x;
    LIMIT
}

/// The false direction of [`named_const_is_read`]: a wrong inlined value would prove
/// this.
/// requires: true
/// ensures: ret == 11
pub fn named_const_is_read_cannot_prove_this(x: u8) -> u8 {
    let _ = x;
    LIMIT
}

/// A named constant used as a comparison bound decides. The precondition names the
/// value the constant holds (`10`) as a plain literal, which is the spelling that
/// worked before the contract reader could resolve `const` items; the constant
/// itself is named in the `A contract that names a const` section below. A wrong
/// inlined value would make the branch unreachable and the postcondition false.
/// requires: x < 10
/// ensures: ret == 1
pub fn named_const_bounds_a_comparison(x: u8) -> u8 {
    if x < LIMIT {
        1
    } else {
        2
    }
}

/// The false direction of [`named_const_bounds_a_comparison`].
/// requires: x < 10
/// ensures: ret == 2
pub fn named_const_bounds_a_comparison_cannot_prove_this(x: u8) -> u8 {
    if x < LIMIT {
        1
    } else {
        2
    }
}

/// A named constant used in an equality test decides.
/// requires: x == 10
/// ensures: ret == 1
pub fn named_const_matches_an_equality(x: u8) -> u8 {
    if x == LIMIT {
        1
    } else {
        2
    }
}

/// The false direction of [`named_const_matches_an_equality`].
/// requires: x == 10
/// ensures: ret == 2
pub fn named_const_matches_an_equality_cannot_prove_this(x: u8) -> u8 {
    if x == LIMIT {
        1
    } else {
        2
    }
}

/// A constant whose definition is an *expression* rather than a literal is not
/// inlined: rustc prints it with its own body and locals (`const NEXT: u8 = {
/// let mut _0: u8; ... }`), so the use site stays an unreadable path constant and
/// the contract is not decided. This is a coverage boundary, not a wrong proof --
/// the value is simply absent, so nothing is proved either way. Inlining it would
/// mean interpreting the item's body, which the executor already knows how to do
/// for a function; that is future work, and this entry is the pin that says the
/// boundary is where it is.
/// requires: true
/// ensures: ret == 11
pub fn named_const_of_an_expression_is_not_inlined(x: u8) -> u8 {
    let _ = x;
    NEXT
}

/// A constant wider than a byte keeps its own width.
/// requires: true
/// ensures: ret == 1000
pub fn named_const_keeps_its_width() -> u16 {
    WIDE_LIMIT
}

/// The false direction of [`named_const_keeps_its_width`].
/// requires: true
/// ensures: ret == 999
pub fn named_const_keeps_its_width_cannot_prove_this() -> u16 {
    WIDE_LIMIT
}

/// A boolean constant selects a branch at the use site.
/// requires: true
/// ensures: ret == 7
pub fn named_bool_const_selects() -> u8 {
    if ENABLED {
        7
    } else {
        9
    }
}

/// The false direction of [`named_bool_const_selects`].
/// requires: true
/// ensures: ret == 9
pub fn named_bool_const_selects_cannot_prove_this() -> u8 {
    if ENABLED {
        7
    } else {
        9
    }
}

/// A negative constant's sign survives inlining, so the comparison is a signed one.
/// requires: x >= -1
/// ensures: ret == 1
pub fn named_negative_const_is_signed(x: i8) -> i8 {
    if x < NEG {
        0
    } else {
        1
    }
}

/// The false direction of [`named_negative_const_is_signed`]: reading `NEG` as a
/// positive 1 would make this hold for `x == -1` and `x == 0`, so it is not the
/// false twin of a wrong *value* alone -- it also pins the signed reading.
/// requires: x >= -1
/// ensures: ret == 0
pub fn named_negative_const_is_signed_cannot_prove_this(x: i8) -> i8 {
    if x < NEG {
        0
    } else {
        1
    }
}

/// Two modules with a `const` of the same last name. rustc prints the definitions
/// as `const low::K: u8 = const 5_u8;` and the uses as `const low::K`, so keying
/// the table by the full path is what keeps them apart -- a table keyed by the
/// last segment would collapse them and could read the wrong value.
pub mod low {
    /// The low limit.
    pub const K: u8 = 5;
}

/// A second module whose `const K` has a different value.
pub mod high {
    /// The high limit.
    pub const K: u8 = 7;
}

/// A module-nested constant is inlined by its full path.
/// requires: true
/// ensures: ret == 5
pub fn nested_module_const_is_read() -> u8 {
    low::K
}

/// The false direction of [`nested_module_const_is_read`]: reading the *other*
/// module's `K` (7) would prove this, so the entry pins the path keying.
/// requires: true
/// ensures: ret == 7
pub fn nested_module_const_is_read_cannot_prove_this() -> u8 {
    low::K
}

/// A `const` declared *inside* a function body is not inlined, because the two
/// spellings do not meet: the *use* is printed with the enclosing function's path
/// (`const a_function_local_const_is_not_inlined::L`) while the *definition* is
/// printed bare (`const L: u8 = const 3_u8;`). It stays an unreadable path
/// constant, a coverage boundary rather than a wrong proof, since no value is read
/// at all.
///
/// The bare definition is *also* why a function-local item must not become a
/// program-wide key: a crate-level `const` gets the same bare definition, so the
/// definition alone cannot tell the two apart. Only the use site can -- a crate
/// item is used bare (`const L`), a local one qualified (`const f::L`) -- which is
/// what [`bare_const_uses`] reads. See
/// [`a_local_const_is_not_in_scope_in_another_function`] for the false proof a bare
/// key would reopen.
/// requires: true
/// ensures: ret == 3
pub fn a_function_local_const_is_not_inlined() -> u8 {
    const L: u8 = 3;
    L
}

/// The function that owns the local `const` the contract below must not see.
/// requires: true
/// ensures: ret == 3
pub fn a_local_const_owner() -> u8 {
    const L: u8 = 3;
    L
}

/// A function-local `const` is not in scope in another function, and its
/// definition must not become a program-wide key.
///
/// The owner's dump prints `const L: u8 = const 3_u8;` bare, while its *use* is
/// qualified (`const a_local_const_owner::L`) -- exactly the spelling a crate-level
/// `const` gets for its definition. The two are indistinguishable from the
/// definition alone, so a bare key recorded for the local let this contract's
/// `requires: L == 3` resolve to a name this function's own source could not
/// write, and the function was *proved* from another function's body. That is not
/// a lost proof but a wrong one: the name must resolve to nothing here, leaving
/// this `Skipped` (unreadable `requires`), never `Verified`.
/// requires: L == 3
/// ensures: ret == 3
pub fn a_local_const_is_not_in_scope_in_another_function() -> u8 {
    3
}

// ---------------------------------------------------------------------------
// A contract that names a `const`
//
// The reader resolves a bare name against the arguments, then against the
// program's own `const` table -- the *same* table the executor folds a body's
// `const LIMIT` from. One table means the contract and the body cannot disagree:
// `requires: x <= LIMIT` and the body's `if x > LIMIT` read one value, because
// there is one value, taken once from rustc's const-evaluated dump. The value is
// built at the item's own width and sign (the dump prints `const 10_u8`), so a
// `const NEG: i8 = -1` compares as `-1`, not `255`.

/// A precondition that names a constant, and a body that names the same one. The
/// postcondition is only reachable when the reader resolves `LIMIT` to `10` on
/// both sides; a bare name that resolved to nothing would skip the function
/// rather than prove it.
/// requires: x <= LIMIT
/// ensures: ret <= LIMIT
pub fn a_contract_names_a_const(x: u8) -> u8 {
    if x > LIMIT {
        LIMIT
    } else {
        x
    }
}

/// The false direction of [`a_contract_names_a_const`]: the body does *not* clamp
/// to `LIMIT`, so the postcondition that names the constant is false. Reading the
/// constant as an unbounded argument would leave this unproved either way, so the
/// entry pins that the name really is a value.
/// requires: true
/// ensures: ret <= LIMIT
pub fn a_contract_names_a_const_cannot_prove_this(x: u8) -> u8 {
    x
}

/// A negative constant named in a contract keeps its sign, so the bound is the
/// signed `-1`. Read as the unsigned `255`, the precondition would be vacuous and
/// the postcondition false.
/// requires: y >= NEG
/// ensures: ret >= NEG
pub fn a_contract_names_a_negative_const(y: i8) -> i8 {
    if y < NEG {
        NEG
    } else {
        y
    }
}

/// A boolean constant named in a comparison in a contract.
/// requires: b == ENABLED
/// ensures: ret == ENABLED
pub fn a_contract_names_a_bool_const(b: bool) -> bool {
    let _ = b;
    ENABLED
}

/// A module-qualified constant named in a contract, resolved by its full path so
/// it does not collide with a top-level constant of the same last segment. The
/// body reads `low::K`, and the contract names the same path.
/// requires: x <= low::K
/// ensures: ret <= low::K
pub fn a_contract_names_a_qualified_const(x: u8) -> u8 {
    if x > low::K {
        low::K
    } else {
        x
    }
}

/// The false direction of [`a_contract_names_a_qualified_const`]: naming the
/// *other* module's `K` (7) is a value the body never exceeds, but the body clamps
/// to `low::K` (5), so `ret <= high::K` is true -- this entry instead pins the two
/// values apart by demanding the body reach `high::K`, which it cannot.
/// requires: x <= low::K
/// ensures: ret == high::K
pub fn a_contract_names_a_qualified_const_cannot_prove_this(x: u8) -> u8 {
    if x > low::K {
        low::K
    } else {
        x
    }
}

/// A constant whose definition is an *expression* is refused when a contract
/// names it, rather than guessed at: its value lives in its own body, which the
/// contract reader does not fold. The refusal is a skip, so nothing is proved --
/// which is the honest answer, not a wrong proof.
/// requires: x <= NEXT
/// ensures: ret <= NEXT
pub fn a_contract_names_an_expression_const(x: u8) -> u8 {
    let _ = x;
    NEXT
}

/// A misspelled constant is refused, not read as an argument that does not exist
/// nor as zero. The name here differs from `LIMIT` by one letter.
/// requires: x <= LIMITT
/// ensures: ret <= LIMIT
pub fn a_misspelled_const_is_refused(x: u8) -> u8 {
    let _ = x;
    LIMIT
}

/// A struct whose methods carry contracts, so a contract attached to an
/// *inherent method* is exercised at all.
pub struct MethodCounter {
    pub n: u8,
}

impl MethodCounter {
    /// A method's contract is keyed by the source name `bump`, but the MIR dump
    /// names the body `<impl at …>::bump`. Resolving the contract by the *dump*
    /// name matched nothing, and a missing contract is not a refusal:
    /// `verify_function` builds `requires` and `ensures` from it, so the method
    /// was checked against `true` and *no* postcondition -- reported verified with
    /// zero obligations, the body never looked at. The true direction must verify
    /// *with* its postcondition checked, which is why the obligation count is
    /// asserted rather than only the verdict.
    /// requires: self.n <= 250
    /// ensures: ret == self.n + 1
    pub fn bump(&self) -> u8 {
        self.n + 1
    }

    /// The false direction of [`MethodCounter::bump`]: the postcondition demands
    /// one more than the body returns, so it is false on every input. Before the
    /// tail resolution this came back `verified` with zero obligations -- the exact
    /// false proof the resolution closes. The corpus-wide naming invariant holds
    /// it as well.
    /// requires: self.n <= 250
    /// ensures: ret == self.n + 2
    pub fn bump_cannot_prove_this(&self) -> u8 {
        self.n + 1
    }
}

// ---------------------------------------------------------------------------
// A string literal must not leak a function-local `const`
//
// The bare-use scan reads use sites out of the dump to tell a crate-level
// `const` from a function-local one. A `debug s => const "const LEAKY";` binding
// (and the `alloc` block that backs the string) spells `const LEAKY` as *data*,
// not as a use, but a scan that reads the raw line sees the same letters. That
// made the local `LEAKY` look bare-used, gave it a program-wide key, and let this
// contract resolve a name its own source could not write -- the very false proof
// the qualified-use test exists to prevent, reopened through a string.
//
// The local name must be *unique* among the file's locals for the shape to
// appear: rustc qualifies a local `const`'s definition (`const f::L`) only when
// another local shares its name, and prints it bare (`const LEAKY`) when it does
// not -- and the bare spelling is the one that collides with a crate-level item.

/// A function whose local `const` no other local shares, so rustc prints its
/// *definition* bare (`const LEAKY: u8 = const 3_u8;`) -- byte-identical to a
/// crate-level item's.
/// requires: true
/// ensures: ret == 3
pub fn a_unique_local_const_owner() -> u8 {
    const LEAKY: u8 = 3;
    LEAKY
}

/// A string that contains the text `const LEAKY`, so the leak shape is present.
/// requires: true
/// ensures: ret == 0
pub fn a_string_literal_spells_const_leaky() -> u8 {
    let s = "const LEAKY";
    let _ = s;
    0
}

/// A contract that names `LEAKY` where no `const LEAKY` is in scope. The only
/// `const LEAKY` is a local of [`a_unique_local_const_owner`], reachable here only
/// if a string literal leaked its name into the bare-use set. It must be
/// `Skipped`, never `Verified`.
/// requires: LEAKY == 3
/// ensures: ret == 3
pub fn a_string_literal_must_not_leak_a_unique_local_const() -> u8 {
    3
}

// ---------------------------------------------------------------------------
// A crate-level `const` a *contract* names but no body uses
//
// The bare-use test is silent for a crate-level constant that only a contract
// names: there is no use site to read. The definition alone cannot say the item
// is module-scoped, so it was dropped and the contract went unreadable -- a lost
// proof, not a wrong one. The source knows the item is at brace depth zero, so
// `spec::crate_level_consts` says so and the definition is kept.

/// A crate-level constant named by a contract below and by no body at all.
const CONTRACT_ONLY: u8 = 7;

/// The postcondition names [`CONTRACT_ONLY`], which the body never reads. It must
/// resolve and the function verify; before the crate-scope tell the definition
/// was dropped and this was `Skipped` (unreadable `ensures`).
/// requires: true
/// ensures: ret <= CONTRACT_ONLY
pub fn a_contract_only_const_is_resolved() -> u8 {
    3
}

// ---------------------------------------------------------------------------
// Recursion and the intrinsic dispatch order
//
// `try_recursive_call` runs before the intrinsic model. A function named exactly
// like an intrinsic that calls the *intrinsic* (`u8::wrapping_add`) is not calling
// itself, but a resolver that matched on the last `::` component saw the tail
// `wrapping_add`, took the call for a self-call, and answered it from this
// function's own postcondition instead of evaluating the intrinsic -- a false
// proof. The resolver now also requires the method's `self` type to agree, so
// `u8` and the local function are distinct.
//
// The name must be the intrinsic's *exact* tail for the shape to appear: rustc
// prints a call to the intrinsic as `core::num::<impl u8>::wrapping_add`, so only
// a local item whose last segment is `wrapping_add` collides with it. A `decreases:`
// measure is also required, because the false proof is the recursion route
// assuming the postcondition; without a measure that route never fires.

/// A free function named exactly `wrapping_add` that calls the *intrinsic* on the
/// non-base path. Its postcondition `ret == 0` is false for `n == 1` (the body
/// returns `0u8.wrapping_add(1) == 1`), so it must FAIL. Treating the intrinsic
/// call as a self-call assumed `ret == 0` for the result and proved it.
/// requires: true
/// decreases: n
/// ensures: ret == 0
pub fn wrapping_add(n: u8) -> u8 {
    if n == 0 {
        0
    } else {
        0u8.wrapping_add(n)
    }
}

/// A free function named exactly `wrapping_add` that *does* call itself. The
/// type-aware resolver must still fire the recursion: the call `wrapping_add(n-1)`
/// is printed bare (`wrapping_add`), matches this function by exact name, and its
/// postcondition is assumed by the induction. This is the companion to the fixture
/// above -- the intrinsic guard must not refuse a real self-call just because the
/// tail matches an intrinsic name.
/// requires: true
/// decreases: n
/// ensures: ret <= n
pub fn wrapping_add_still_recurses(n: u8) -> u8 {
    if n == 0 {
        0
    } else {
        wrapping_add_still_recurses(n - 1)
    }
}

/// A static associated function genuinely named like an intrinsic that recurses on
/// itself. The tail matches an intrinsic's, but the call `Recursing::wrapping_sub`
/// resolves to this function -- a `core` intrinsic's name carries an `<impl`
/// projection and is refused -- so the induction proves the claim. The name is
/// `wrapping_sub` rather than `wrapping_add` because the free `wrapping_add` above
/// already owns that outcome key, and a method's report name is its bare tail.
/// requires: true
/// ensures: ret <= x
pub fn a_static_method_named_like_an_intrinsic_still_recurses(x: u8) -> u8 {
    Recursing::wrapping_sub(x)
}

/// The receiver for [`a_static_method_named_like_an_intrinsic_still_recurses`].
pub struct Recursing;

impl Recursing {
    /// Recurses on `x`, with a measure and a postcondition the induction proves.
    /// requires: true
    /// decreases: x
    /// ensures: ret <= x
    pub fn wrapping_sub(x: u8) -> u8 {
        if x == 0 {
            0
        } else {
            Recursing::wrapping_sub(x - 1)
        }
    }
}

// ---------------------------------------------------------------------------
// A recursive contract that names a `const`
//
// The recursive call evaluates the callee's contract with the *call site's*
// argument bindings, but a constant is the same at the call as at entry. Handing
// the reader an empty `const` table there made `requires: n <= LIMIT` unreadable
// at the self-call, so a decidable proof came back a refusal.

/// A recursive function whose contract names [`LIMIT`]. The constant resolves at
/// the self-call now, so the induction goes through and this verifies; before,
/// the self-call's `requires` was unreadable and the function was `Skipped`.
/// requires: n <= LIMIT
/// decreases: n
/// ensures: ret <= LIMIT
pub fn a_recursive_contract_naming_a_const_is_resolved(n: u8) -> u8 {
    if n == 0 {
        0
    } else if n > LIMIT {
        0
    } else {
        a_recursive_contract_naming_a_const_is_resolved(n - 1)
    }
}
