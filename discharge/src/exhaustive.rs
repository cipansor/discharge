//! Complete verification by exhaustive enumeration.
//!
//! The BDD engine in [`crate::smt`] is *symbolic*: it reasons about a formula
//! without touching every input, but it can hit a size wall. This module is the
//! opposite trade-off: for small domains it walks **every** input, which is a
//! complete proof with no size wall and no `Unknown` verdict. It is the same
//! technique used to validate flight-control tables.
//!
//! The functions here take real, executable Rust functions (not symbolic terms),
//! so a successful run proves a property of the *actual compiled code path* you
//! would ship.

/// A type whose value space is small enough to enumerate completely.
pub trait Exhaustive: Copy {
    /// Invoke `f` for every value of the type. Stops early if `f` returns
    /// `Some(x)`, returning that `x`.
    fn for_each_find<T>(f: &mut dyn FnMut(Self) -> Option<T>) -> Option<T>;
}

macro_rules! impl_exhaustive_unsigned {
    ($($t:ty),*) => {$(
        impl Exhaustive for $t {
            fn for_each_find<T>(f: &mut dyn FnMut(Self) -> Option<T>) -> Option<T> {
                let mut v: $t = 0;
                loop {
                    if let Some(x) = f(v) {
                        return Some(x);
                    }
                    match v.checked_add(1) {
                        Some(n) => v = n,
                        None => return None,
                    }
                }
            }
        }
    )*};
}

impl_exhaustive_unsigned!(u8, u16, u32);

/// `true` iff `p` holds for every `u8`. A complete proof by enumeration.
pub fn for_all_u8(p: impl Fn(u8) -> bool) -> bool {
    let mut f = |v: u8| if p(v) { None } else { Some(()) };
    u8::for_each_find(&mut f).is_none()
}

/// `true` iff `p` holds for every `u16`. 65 536 cases.
pub fn for_all_u16(p: impl Fn(u16) -> bool) -> bool {
    let mut f = |v: u16| if p(v) { None } else { Some(()) };
    u16::for_each_find(&mut f).is_none()
}

/// `true` iff `p` holds for every `u32`. 4.29 billion cases; only run this when
/// the property is cheap and you really mean it.
pub fn for_all_u32(p: impl Fn(u32) -> bool) -> bool {
    let mut f = |v: u32| if p(v) { None } else { Some(()) };
    u32::for_each_find(&mut f).is_none()
}

/// Return the smallest `u8` violating `p`, or `None` if `p` is a theorem.
pub fn find_violation_u8(p: impl Fn(u8) -> bool) -> Option<u8> {
    let mut f = |v: u8| if p(v) { None } else { Some(v) };
    u8::for_each_find(&mut f)
}

/// Return the smallest `u16` violating `p`, or `None` if `p` is a theorem.
pub fn find_violation_u16(p: impl Fn(u16) -> bool) -> Option<u16> {
    let mut f = |v: u16| if p(v) { None } else { Some(v) };
    u16::for_each_find(&mut f)
}

/// `true` iff the binary predicate holds for every pair of `u8`s (65 536 cases).
pub fn for_all_u8_2(p: impl Fn(u8, u8) -> bool) -> bool {
    for_all_u8(|a| for_all_u8(|b| p(a, b)))
}

/// `true` iff the binary predicate holds for every pair of `u16`s. This is
/// 2^32 cases and is included for completeness; prefer the symbolic engine for
/// wide domains.
pub fn for_all_u16_2(p: impl Fn(u16, u16) -> bool) -> bool {
    for_all_u16(|a| for_all_u16(|b| p(a, b)))
}

/// The smallest `(a, b)` pair of `u8`s violating `p`, if any.
pub fn find_violation_u8_2(p: impl Fn(u8, u8) -> bool) -> Option<(u8, u8)> {
    let mut f = |a: u8| {
        let mut g = |b: u8| if p(a, b) { None } else { Some(b) };
        u8::for_each_find(&mut g).map(|b| (a, b))
    };
    u8::for_each_find(&mut f)
}

/// The smallest `(a, b)` pair of `u16`s violating `p`, if any.
pub fn find_violation_u16_2(p: impl Fn(u16, u16) -> bool) -> Option<(u16, u16)> {
    let mut f = |a: u16| {
        let mut g = |b: u16| if p(a, b) { None } else { Some(b) };
        u16::for_each_find(&mut g).map(|b| (a, b))
    };
    u16::for_each_find(&mut f)
}
