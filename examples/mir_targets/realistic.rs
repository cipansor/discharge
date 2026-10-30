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
