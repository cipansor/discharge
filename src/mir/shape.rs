//! A small, comparable summary of a MIR dump — the unit the `rustc_public`
//! oracle checks the text frontend against.
//!
//! The frontend's known weakness (README, "The known gaps", gap 2) is that it
//! reads the *textual* `--emit=mir` dump rather than linking `rustc`. A rustc
//! release that changes the pretty-printer can therefore break the parser, and
//! the parser would be the only thing that noticed — which is to say, nothing
//! would.
//!
//! This module defines the smallest summary that is both
//!
//! * derivable from the text dump by the frontend's own parser, and
//! * derivable from the *typed* MIR by `rustc_public` in
//!   `tools/mir-oracle`,
//!
//! so the two can be compared. The oracle lives in a separate crate on purpose:
//! linking `rustc` internals needs `#![feature(rustc_private)]` and the nightly
//! `rustc-dev` component, and neither may leak into a crate that must build on
//! stable with no dependencies. So this crate exposes the summary as plain data
//! ([`FnShape`]), the oracle computes the same shape from the compiler's own IR,
//! and the gate fails if they disagree.
//!
//! What is compared is deliberately structural, not textual: how many basic
//! blocks each function lowered to, and which panic conditions `rustc` inserted,
//! in block order. Those are facts about the program, not about the printer, so
//! a match is real evidence and a mismatch points at the parser rather than at
//! whitespace.

use std::collections::BTreeMap;

use crate::mir::parse::{self, Term};

/// The kind of panic `rustc` guards against, normalised so the two MIR sources
/// can be compared without comparing their printers.
///
/// The variants mirror `rustc`'s own `AssertMessage` for the operations this
/// frontend models. `Other` carries the raw message for anything else, so a
/// shape mismatch is still diagnosable rather than silently dropped — and so
/// that an unmodelled assert is *visible* instead of absent.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum PanicKind {
    /// `a + b` overflow.
    OverflowAdd,
    /// `a - b` underflow.
    OverflowSub,
    /// `a * b` overflow.
    OverflowMul,
    /// `a / b` overflow, i.e. `MIN / -1`.
    OverflowDiv,
    /// `a % b` overflow, i.e. `MIN % -1`.
    OverflowRem,
    /// `-a` overflow, i.e. `-MIN`.
    OverflowNeg,
    /// A zero divisor in `/`.
    DivByZero,
    /// A zero divisor in `%`.
    RemByZero,
    /// A shift by at least the width.
    ShiftLeft,
    /// A right shift by at least the width.
    ShiftRight,
    /// An array or slice index past the end.
    Bounds,
    /// Anything else, carrying `rustc`'s message so it is not lost.
    Other(String),
}

impl PanicKind {
    /// Classify the message `rustc` prints inside `assert(…)` in a text dump.
    ///
    /// The text dump spells these out, with the operator inline in the template:
    ///
    /// ```text
    /// assert(!move (_5.1: bool), "attempt to compute `{} - {}`, which would overflow", …)
    /// assert(!move _6, "attempt to divide `{}` by zero", …)
    /// ```
    ///
    /// so this matches on the operator glyph and the verb. It is deliberately
    /// tolerant of the surrounding wording — a rustc release that reflows the
    /// sentence but keeps `` `{} - {}` `` still classifies — but it is *not*
    /// tolerant of the operator, because that is the fact being compared.
    pub fn from_text_message(msg: &str) -> PanicKind {
        let has = |s: &str| msg.contains(s);
        if has("by zero") || has("divisor of zero") {
            if has("remainder") {
                PanicKind::RemByZero
            } else {
                PanicKind::DivByZero
            }
        } else if has("negate") {
            PanicKind::OverflowNeg
        } else if has("shift left") {
            PanicKind::ShiftLeft
        } else if has("shift right") {
            PanicKind::ShiftRight
        } else if has("index out of bounds") || has("slice index") {
            PanicKind::Bounds
        } else if has("{} - {}") {
            PanicKind::OverflowSub
        } else if has("{} + {}") {
            PanicKind::OverflowAdd
        } else if has("{} * {}") {
            PanicKind::OverflowMul
        } else if has("{} / {}") {
            PanicKind::OverflowDiv
        } else if has("{} % {}") {
            PanicKind::OverflowRem
        } else {
            PanicKind::Other(msg.to_string())
        }
    }
}

/// Which way round an assert's condition is: whether the panic fires on the
/// condition being *true* or *false*.
///
/// This is a separate field from [`PanicKind`] because the two are independent
/// and both are load-bearing. `PanicKind` says *what* the guard is about — an
/// addition overflow, a zero divisor — and the polarity says whether `rustc`
/// printed the condition or its negation. rustc prints
/// `assert(!move _3, "…")` for the arithmetic guards, so the *same* message with
/// the `!` flipped describes the opposite program: one reports an overflowing add
/// as a panic, the other reports every non-overflowing add as a panic and misses
/// the overflowing one.
///
/// Recording only the message let a printer change that flipped a leading `!`
/// leave both block count and panic kind identical, so the oracle agreed while
/// the frontend checked the opposite guard. The frontend's parser has always
/// carried this (`Term::Assert { negated, … }`); the shape did not, which is
/// exactly the gap.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum Polarity {
    /// `assert(cond, …)`: the panic fires when `cond` is false.
    True,
    /// `assert(!cond, …)`: the panic fires when `cond` is true.
    Negated,
}

impl Polarity {
    /// The polarity for a parsed leading `!`.
    pub const fn from_negated(negated: bool) -> Self {
        if negated {
            Polarity::Negated
        } else {
            Polarity::True
        }
    }
}

/// One panic guard: what it guards against, and which way round its condition is.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct AssertShape {
    /// The condition `rustc` is guarding, normalised.
    pub kind: PanicKind,
    /// Whether the panic fires on the condition being true or false.
    pub polarity: Polarity,
}

/// The comparable summary of one function.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct FnShape {
    /// How many basic blocks the function lowered to.
    pub blocks: usize,
    /// The panic guards `rustc` inserted, in `(block, order within block)` order,
    /// each with its polarity.
    pub panics: Vec<AssertShape>,
}

/// The summaries of every function in a text MIR dump, grouped by bare name.
///
/// The key is the last path segment (`actuator::clamp` and `clamp` both key as
/// `clamp`) because the two MIR sources spell the path differently and the point
/// is to compare the functions, not their qualified names.
///
/// The value is a **list**, not one shape, because a bare name is not unique:
/// `impl A { fn check(…) }` and `impl B { fn check(…) }` in one file both key as
/// `check`. A single-slot map silently kept whichever came last, so a regression
/// in the dropped method was invisible. Keeping every shape and comparing the
/// groups as multisets is what makes a lost or altered method show up, and it
/// does not depend on the two sides agreeing about qualified names or about the
/// order the functions appear in.
pub fn of_text_mir(mir: &str) -> BTreeMap<String, Vec<FnShape>> {
    let program = parse::parse_program(mir);
    let mut out: BTreeMap<String, Vec<FnShape>> = BTreeMap::new();
    for f in &program.fns {
        let mut panics = Vec::new();
        // `blocks` is in dump order, and each block's statements and terminator
        // are in order, so the panic list is deterministic.
        for block in &f.blocks {
            if let Term::Assert { msg, negated, .. } = &block.term {
                panics.push(AssertShape {
                    kind: PanicKind::from_text_message(msg),
                    polarity: Polarity::from_negated(*negated),
                });
            }
        }
        let key = f.name.rsplit("::").next().unwrap_or(&f.name).to_string();
        out.entry(key).or_default().push(FnShape {
            blocks: f.blocks.len(),
            panics,
        });
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The text classifier, pinned against the exact strings `rustc --emit=mir`
    /// prints. These are copied from a real dump rather than invented, because
    /// the whole risk this module manages is that the wording moves.
    #[test]
    fn classifies_rustc_text_messages() {
        let cases = [
            ("attempt to compute `{} - {}`, which would overflow", PanicKind::OverflowSub),
            ("attempt to compute `{} + {}`, which would overflow", PanicKind::OverflowAdd),
            ("attempt to compute `{} * {}`, which would overflow", PanicKind::OverflowMul),
            ("attempt to compute `{} / {}`, which would overflow", PanicKind::OverflowDiv),
            ("attempt to compute `{} % {}`, which would overflow", PanicKind::OverflowRem),
            ("attempt to negate `{}`, which would overflow", PanicKind::OverflowNeg),
            ("attempt to divide `{}` by zero", PanicKind::DivByZero),
            ("attempt to calculate the remainder with a divisor of zero", PanicKind::RemByZero),
            ("attempt to shift left by `{}`, which would overflow", PanicKind::ShiftLeft),
            ("attempt to shift right by `{}`, which would overflow", PanicKind::ShiftRight),
            ("index out of bounds: the len is {} but the index is {}", PanicKind::Bounds),
        ];
        for (msg, want) in cases {
            assert_eq!(PanicKind::from_text_message(msg), want, "message: {msg}");
        }
    }

    /// A message the classifier does not recognise is kept, not discarded: an
    /// unmodelled panic must still compare unequal to a typed-side `Other`, so
    /// it fails the oracle rather than passing by omission.
    #[test]
    fn an_unknown_message_is_preserved() {
        let kind = PanicKind::from_text_message("something entirely new");
        assert_eq!(kind, PanicKind::Other("something entirely new".to_string()));
    }

    /// The block count is read from the parsed IR, and a two-arm branch is what
    /// makes it more than one — a smoke test that the shape is actually populated
    /// rather than always zero.
    #[test]
    fn shape_counts_blocks_from_a_real_dump() {
        let dump = "\
fn simple(_1: u32, _2: u32) -> u32 {
    let mut _0: u32;
    let mut _3: bool;

    bb0: {
        _3 = Lt(_1, _2);
        switchInt(move _3) -> [0: bb2, otherwise: bb1];
    }

    bb1: {
        _0 = _1;
        goto -> bb2;
    }

    bb2: {
        return;
    }
}
";
        let shapes = of_text_mir(dump);
        let s = shapes.get("simple").expect("function parsed");
        assert_eq!(s.len(), 1, "one function named `simple`");
        assert_eq!(s[0].blocks, 3);
        assert!(s[0].panics.is_empty());
    }

    /// The polarity is carried and is separate from the kind. A dump whose guard
    /// is `assert(!…)` must not shape the same as one whose guard is `assert(…)`
    /// with the same message, because they describe opposite programs.
    #[test]
    fn polarity_is_recorded_and_distinguishes_inverted_guards() {
        let dump = |cond: &str| {
            format!(
                "\
fn checked(_1: u32, _2: u32) -> u32 {{
    let mut _0: u32;
    let mut _3: bool;

    bb0: {{
        _3 = AddWithOverflow(_1, _2);
        assert({cond}move (_3.1: bool), \"attempt to compute `{{}} + {{}}`, which would overflow\") -> [success: bb1, unwind continue];
    }}

    bb1: {{
        _0 = _1;
        return;
    }}
}}
"
            )
        };
        let normal = of_text_mir(&dump(""));
        let inverted = of_text_mir(&dump("!"));

        let n = &normal.get("checked").unwrap()[0];
        let i = &inverted.get("checked").unwrap()[0];
        assert_eq!(n.panics.len(), 1);
        assert_eq!(n.panics[0].kind, PanicKind::OverflowAdd);
        assert_eq!(i.panics[0].kind, PanicKind::OverflowAdd);
        assert_eq!(n.panics[0].polarity, Polarity::True);
        assert_eq!(i.panics[0].polarity, Polarity::Negated);
        assert_ne!(
            n, i,
            "flipping the `!` must change the shape, or the oracle cannot see it"
        );
    }

    /// Two methods with the same bare name must both survive. The old single-slot
    /// map kept only the last, so a regression in the dropped one was invisible.
    #[test]
    fn same_named_functions_are_both_kept() {
        let dump = "\
fn check(_1: u32, _2: u32) -> u32 {
    let mut _0: u32;

    bb0: {
        _0 = _1;
        return;
    }
}

fn check(_1: u32) -> u32 {
    let mut _0: u32;
    let mut _2: u32;

    bb0: {
        _0 = _1;
        return;
    }

    bb1: {
        return;
    }
}
";
        let shapes = of_text_mir(dump);
        let group = shapes.get("check").expect("both methods present");
        assert_eq!(group.len(), 2, "both `check`s must be kept, not overwritten");
        let mut blocks: Vec<usize> = group.iter().map(|s| s.blocks).collect();
        blocks.sort_unstable();
        assert_eq!(blocks, vec![1, 2], "each shape is kept distinctly");
    }
}
