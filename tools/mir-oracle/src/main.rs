//! A `rustc_public` oracle for the text-MIR frontend.
//!
//! `discharge`'s MIR frontend reads the *textual* `--emit=mir` dump. That is a
//! deliberate choice (no `rustc-dev` dependency, inspectable input), and its
//! stated cost is that a rustc release which changes the pretty-printer can
//! break the parser, and only the parser would notice. This tool is the answer
//! to that cost: it asks `rustc` for the **same program's typed MIR** through
//! `rustc_public`, summarises both, and fails if the summaries disagree.
//!
//! ```text
//!   rustc --emit=mir  ──► text ──► discharge::mir::shape ──┐
//!                                                          ├──► compare
//!   rustc_public      ──► typed MIR ──► shape (this file) ──┘
//! ```
//!
//! It is a separate crate because it links rustc internals: it needs
//! `#![feature(rustc_private)]`, a nightly toolchain, and the `rustc-dev`
//! component. None of those may touch `discharge`, which must build on stable
//! with zero dependencies. The dependency arrow points one way — this crate
//! depends on `discharge`, never the reverse — so the oracle can never become
//! part of what ships.
//!
//! # What is compared, and why this and not the text
//!
//! The typed MIR dump is not byte-identical to `--emit=mir` output: the typed
//! one omits `copy` qualifiers, prints `let  _4` with different spacing, and
//! nests `scope` blocks. Comparing the *text* would therefore fail on cosmetics
//! and tell us nothing. What the frontend actually depends on is the *structure*
//! of each function — how many basic blocks it has, and which panic conditions
//! `rustc` inserted and in what order. That is a fact about the program, not
//! about the printer, so a match is real evidence and a mismatch points at the
//! parser rather than at whitespace.
//!
//! # Usage
//!
//! ```console
//! $ DISCHARGE_RUSTC=$(rustup which --toolchain nightly rustc) \
//!     cargo run -p mir-oracle -- examples/mir_targets/actuator.rs
//! actuator.rs: 30 functions, 30 shapes agree, 0 differ
//! ```
//!
//! Exit status: `0` if every shape agrees, `1` if any differs, `2` if the tool
//! could not run (no nightly, no `rustc-dev`). The last case is distinct on
//! purpose: "the oracle did not run" is not evidence about the parser.

#![feature(rustc_private)]
#![deny(missing_docs)]

extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_public;

use std::collections::BTreeMap;
use std::path::Path;

use rustc_public::mir::{AssertMessage, Body, TerminatorKind};
use rustc_public::CrateDef;

use discharge::mir::shape::{AssertShape, FnShape, PanicKind, Polarity};

/// The shape of one function, computed from `rustc`'s own typed MIR.
///
/// This is the mirror of `discharge::mir::shape::FnShape`, built from the
/// structured IR rather than from printed text, so the two are independent.
fn shape_of_body(body: &Body) -> FnShape {
    let mut panics = Vec::new();
    for block in &body.blocks {
        // A checked arithmetic operation lowers to a statement that *sets* the
        // overflow flag plus an `Assert` terminator that consumes it; the
        // terminator carries the `AssertMessage`, so walking terminators alone
        // finds every panic guard, in the same block order the text dump prints.
        //
        // `expected` is the value of `cond` for which control *continues*: `true`
        // for `assert(cond, …)`, `false` for `assert(!cond, …)`. It is the typed
        // side's copy of the text dump's leading `!`, and it is compared, because
        // the message alone does not distinguish an overflow guard from its
        // inverse -- a printer change that flipped a `!` used to leave the shape
        // identical and the oracle silent.
        if let TerminatorKind::Assert { msg, expected, .. } = &block.terminator.kind {
            panics.push(AssertShape {
                kind: classify(msg),
                polarity: polarity_of(*expected),
            });
        }
    }
    FnShape {
        blocks: body.blocks.len(),
        panics,
    }
}

/// `expected` is the condition value for which control continues, so it is the
/// inverse of the text dump's leading `!`.
fn polarity_of(expected: bool) -> Polarity {
    if expected {
        Polarity::True
    } else {
        Polarity::Negated
    }
}

/// Map `rustc`'s structured `AssertMessage` onto the shared [`PanicKind`].
///
/// This is matched on the *variant*, not on a printed description, so it cannot
/// be fooled by a message that merely mentions an operator. A variant this tool
/// does not model becomes `PanicKind::Other`, which will differ from the text
/// side's classification and so fail the comparison — the intended outcome,
/// because an unmodelled panic is exactly the thing worth knowing about.
fn classify(msg: &AssertMessage) -> PanicKind {
    use rustc_public::mir::BinOp;
    match msg {
        AssertMessage::Overflow(BinOp::Add, _, _) => PanicKind::OverflowAdd,
        AssertMessage::Overflow(BinOp::Sub, _, _) => PanicKind::OverflowSub,
        AssertMessage::Overflow(BinOp::Mul, _, _) => PanicKind::OverflowMul,
        AssertMessage::Overflow(BinOp::Div, _, _) => PanicKind::OverflowDiv,
        AssertMessage::Overflow(BinOp::Rem, _, _) => PanicKind::OverflowRem,
        AssertMessage::Overflow(BinOp::Shl, _, _) => PanicKind::ShiftLeft,
        AssertMessage::Overflow(BinOp::Shr, _, _) => PanicKind::ShiftRight,
        AssertMessage::OverflowNeg(_) => PanicKind::OverflowNeg,
        AssertMessage::DivisionByZero(_) => PanicKind::DivByZero,
        AssertMessage::RemainderByZero(_) => PanicKind::RemByZero,
        AssertMessage::BoundsCheck { .. } => PanicKind::Bounds,
        other => PanicKind::Other(format!("{other:?}")),
    }
}

/// The shapes of every function with a body, grouped by bare name.
///
/// Grouped, not keyed one-to-one: a bare name is not unique (`A::check` and
/// `B::check` both reduce to `check`), and a single-slot map kept only the last,
/// so the oracle checked one method and could not see a regression in the other.
fn typed_shapes(args: &[String]) -> Result<BTreeMap<String, Vec<FnShape>>, String> {
    let mut out: BTreeMap<String, Vec<FnShape>> = BTreeMap::new();
    let result = rustc_public::run!(args, || -> ControlFlow<()> {
        for item in rustc_public::all_local_items() {
            if let Some(body) = item.body() {
                let name = item.name();
                let bare = name.rsplit("::").next().unwrap_or(&name).to_string();
                out.entry(bare).or_default().push(shape_of_body(&body));
            }
        }
        ControlFlow::Continue(())
    });
    result.map_err(|e| format!("rustc_public run failed: {e:?}"))?;
    Ok(out)
}

/// One function where the two sides disagree.
struct Diff {
    name: String,
    text: Vec<FnShape>,
    typed: Vec<FnShape>,
}

/// Compare the text-side and typed-side shapes, returning the functions that
/// disagree.
///
/// A bare name can cover several methods, so each group is compared as a
/// **multiset**: sorted and compared element-wise. Order is not a property worth
/// asserting — the two sides enumerate functions in different orders — but the
/// set of shapes under a name is exactly what a lost or altered method changes.
///
/// Only names the typed side saw are compared. The typed side can miss an item
/// the text side prints (a generic item with no monomorphised body, for one), and
/// that is a coverage gap rather than a parser bug, so it is not a disagreement.
/// A function the *text* side is missing entirely, however, is a parser failure
/// and is reported as a disagreement with an empty text group — silence about a
/// dropped function is the failure mode this whole tool exists to prevent.
fn compare(
    text: &BTreeMap<String, Vec<FnShape>>,
    typed: &BTreeMap<String, Vec<FnShape>>,
) -> (usize, Vec<Diff>) {
    let mut agree = 0usize;
    let mut differ = Vec::new();
    for (name, want) in typed {
        let empty: Vec<FnShape> = Vec::new();
        let got = text.get(name).cloned().unwrap_or(empty);
        let mut got_sorted = got.clone();
        got_sorted.sort();
        let mut want_sorted = want.clone();
        want_sorted.sort();
        if got_sorted == want_sorted {
            agree += 1;
        } else {
            differ.push(Diff {
                name: name.clone(),
                text: got,
                typed: want.clone(),
            });
        }
    }
    (agree, differ)
}

/// Render a group of shapes for the difference report.
fn fmt_group(group: &[FnShape]) -> String {
    if group.is_empty() {
        return "(absent)".to_string();
    }
    group
        .iter()
        .map(|s| format!("{} blocks, panics {:?}", s.blocks, s.panics))
        .collect::<Vec<_>>()
        .join(" | ")
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let Some(target) = args.get(1) else {
        eprintln!("usage: mir-oracle <file.rs>   (set DISCHARGE_RUSTC to a nightly rustc)");
        std::process::exit(2);
    };
    let target = Path::new(target);

    // The text side, exactly as the frontend reads it: `rustc --emit=mir` through
    // the crate's own emitter, so the oracle exercises the real code path rather
    // than a re-implementation of it.
    let text = match discharge::mir::verify::emit_mir(target) {
        Ok(t) => t,
        Err(e) => {
            eprintln!("mir-oracle: could not get text MIR: {e}");
            eprintln!("mir-oracle: set DISCHARGE_RUSTC to a nightly `rustc`");
            std::process::exit(2);
        }
    };
    let text_shapes = discharge::mir::shape::of_text_mir(&text);

    // The typed side, through `rustc_public`. The argument list mirrors what the
    // text emitter passes so both compile the same crate type. `--out-dir` points
    // the compiler's artifacts at a temp directory: without it `rustc` drops
    // `lib<name>.rlib` next to the source, which would litter the repository on
    // every run.
    let out_dir = std::env::temp_dir().join(format!("mir-oracle-{}", std::process::id()));
    let _ = std::fs::create_dir_all(&out_dir);
    let mut typed_args = vec![
        target.to_string_lossy().into_owned(),
        "--edition".to_string(),
        "2021".to_string(),
        "--crate-type".to_string(),
        "lib".to_string(),
        "--out-dir".to_string(),
        out_dir.to_string_lossy().into_owned(),
    ];
    // `run!` expects argv with the program name first, like a real compiler.
    typed_args.insert(0, "mir-oracle".to_string());
    let typed_shapes = match typed_shapes(&typed_args) {
        Ok(s) => s,
        Err(e) => {
            eprintln!("mir-oracle: {e}");
            eprintln!("mir-oracle: needs a nightly with the `rustc-dev` component");
            std::process::exit(2);
        }
    };

    let (agree, differ) = compare(&text_shapes, &typed_shapes);

    let name = target.file_name().map(|s| s.to_string_lossy().into_owned()).unwrap_or_default();
    let typed_fns: usize = typed_shapes.values().map(Vec::len).sum();
    let text_fns: usize = text_shapes.values().map(Vec::len).sum();
    println!(
        "{name}: {typed_fns} functions typed, {text_fns} text, {agree} agree, {} differ",
        differ.len()
    );
    for d in &differ {
        println!("\n  {}:", d.name);
        println!("    text : {}", fmt_group(&d.text));
        println!("    typed: {}", fmt_group(&d.typed));
    }

    if differ.is_empty() {
        std::process::exit(0);
    }
    eprintln!("\nmir-oracle: {} function shape(s) disagree", differ.len());
    std::process::exit(1);
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The structured mapping is what the oracle trusts, so it is pinned
    /// directly: each variant that the frontend models must land on the matching
    /// [`PanicKind`].
    #[test]
    fn structured_assert_messages_map_to_the_shared_kinds() {
        use rustc_public::mir::{BinOp, Operand, Place};
        // The operands do not affect the mapping; `_0` is enough for both.
        let op = || Operand::Copy(Place::from(0usize));

        let add = AssertMessage::Overflow(BinOp::Add, op(), op());
        assert_eq!(classify(&add), PanicKind::OverflowAdd);
        let sub = AssertMessage::Overflow(BinOp::Sub, op(), op());
        assert_eq!(classify(&sub), PanicKind::OverflowSub);
        let mul = AssertMessage::Overflow(BinOp::Mul, op(), op());
        assert_eq!(classify(&mul), PanicKind::OverflowMul);
        let div = AssertMessage::Overflow(BinOp::Div, op(), op());
        assert_eq!(classify(&div), PanicKind::OverflowDiv);
        let rem = AssertMessage::Overflow(BinOp::Rem, op(), op());
        assert_eq!(classify(&rem), PanicKind::OverflowRem);
        let shl = AssertMessage::Overflow(BinOp::Shl, op(), op());
        assert_eq!(classify(&shl), PanicKind::ShiftLeft);
        let shr = AssertMessage::Overflow(BinOp::Shr, op(), op());
        assert_eq!(classify(&shr), PanicKind::ShiftRight);
        let neg = AssertMessage::OverflowNeg(op());
        assert_eq!(classify(&neg), PanicKind::OverflowNeg);
        let dbz = AssertMessage::DivisionByZero(op());
        assert_eq!(classify(&dbz), PanicKind::DivByZero);
        let rbz = AssertMessage::RemainderByZero(op());
        assert_eq!(classify(&rbz), PanicKind::RemByZero);
        let bounds = AssertMessage::BoundsCheck { len: op(), index: op() };
        assert_eq!(classify(&bounds), PanicKind::Bounds);
    }

    /// A variant the frontend does not model must come through as `Other`, so it
    /// surfaces as a disagreement rather than vanishing.
    #[test]
    fn an_unmodelled_assert_message_is_visible_not_dropped() {
        use rustc_public::mir::{Operand, Place};
        let op = || Operand::Copy(Place::from(0usize));
        let null = AssertMessage::NullPointerDereference;
        match classify(&null) {
            PanicKind::Other(msg) => assert!(!msg.is_empty()),
            other => panic!("expected Other, got {other:?}"),
        }
        let _ = op;
    }

    /// The typed side's polarity is the inverse of the text dump's `!`: `expected`
    /// is the value for which control continues. Getting this backwards would make
    /// every arithmetic guard disagree, so it is pinned directly.
    #[test]
    fn expected_maps_to_polarity_inversely() {
        // `assert(cond, …)`: control continues when the condition holds.
        assert_eq!(polarity_of(true), Polarity::True);
        // `assert(!cond, …)`: control continues when the condition does *not* hold,
        // which is how rustc prints the arithmetic guards.
        assert_eq!(polarity_of(false), Polarity::Negated);
    }

    /// The comparison has teeth: identical groups agree, and a single differing
    /// panic kind — or a dropped function — is reported. Without this the tool
    /// could "agree" by comparing nothing.
    #[test]
    fn compare_reports_disagreement_and_absence() {
        let shape = |blocks: usize, panics: Vec<AssertShape>| FnShape { blocks, panics };
        let guard = |kind: PanicKind| AssertShape {
            kind,
            polarity: Polarity::Negated,
        };
        let mut text = BTreeMap::new();
        text.insert("a".to_string(), vec![shape(3, vec![guard(PanicKind::OverflowAdd)])]);
        text.insert("b".to_string(), vec![shape(5, vec![guard(PanicKind::DivByZero)])]);

        let mut typed = BTreeMap::new();
        typed.insert("a".to_string(), vec![shape(3, vec![guard(PanicKind::OverflowAdd)])]);
        typed.insert("b".to_string(), vec![shape(5, vec![guard(PanicKind::RemByZero)])]); // differs
        typed.insert("c".to_string(), vec![shape(2, vec![])]); // absent from text

        let (agree, differ) = compare(&text, &typed);
        assert_eq!(agree, 1, "only `a` agrees");
        let names: Vec<&str> = differ.iter().map(|d| d.name.as_str()).collect();
        assert_eq!(names, vec!["b", "c"]);
        // `c` is reported as an empty text group, not skipped.
        let c = differ.iter().find(|d| d.name == "c").unwrap();
        assert!(c.text.is_empty(), "an absent function reports an empty group");
    }

    /// Flipping only the polarity of a guard must be a disagreement. This is the
    /// regression the polarity field exists to catch: the same message, the
    /// opposite program.
    #[test]
    fn an_inverted_guard_is_a_disagreement() {
        let mut text = BTreeMap::new();
        text.insert(
            "f".to_string(),
            vec![FnShape {
                blocks: 2,
                panics: vec![AssertShape {
                    kind: PanicKind::OverflowAdd,
                    polarity: Polarity::Negated,
                }],
            }],
        );
        let mut typed = text.clone();
        typed.get_mut("f").unwrap()[0].panics[0].polarity = Polarity::True;

        let (agree, differ) = compare(&text, &typed);
        assert_eq!(agree, 0, "the polarity differs, so the shapes must not agree");
        assert_eq!(differ.len(), 1);
    }

    /// Two methods sharing a bare name are compared as a group, so a regression in
    /// either one is caught. The old single-slot map kept only the last.
    #[test]
    fn same_named_methods_are_compared_as_a_group() {
        let a = FnShape { blocks: 2, panics: vec![] };
        let b = FnShape { blocks: 7, panics: vec![] };
        let mut text = BTreeMap::new();
        text.insert("check".to_string(), vec![a.clone(), b.clone()]);
        let mut typed = BTreeMap::new();
        typed.insert("check".to_string(), vec![a.clone(), b.clone()]);

        assert_eq!(compare(&text, &typed).0, 1, "the group matches");

        // Now drop one method on the text side, as a parser regression would.
        let mut lossy = BTreeMap::new();
        lossy.insert("check".to_string(), vec![b.clone()]);
        let (agree, differ) = compare(&lossy, &typed);
        assert_eq!(agree, 0, "losing a same-named method must be reported");
        assert_eq!(differ.len(), 1);
    }
}
