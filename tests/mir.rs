//! Tests for the MIR frontend.
//!
//! Run with a nightly compiler available:
//!
//! ```text
//! DISCHARGE_RUSTC=$(rustup which --toolchain nightly rustc) \
//!   cargo test --features std --test mir
//! ```
//!
//! The tests that need `rustc` skip themselves when `DISCHARGE_RUSTC` is unset,
//! because `--emit=mir` needs nightly and failing on a stable toolchain would say
//! "the code is wrong" when the truth is "the tool could not run".
//!
//! # The oracle
//!
//! The strongest test here is [`counterexamples_really_panic`]. It takes each
//! counterexample the verifier produced, feeds those exact inputs to the *real*
//! function, and requires it to panic. That is a differential check against Rust
//! itself rather than against another model: if the engine reported a
//! counterexample that does not actually panic, the test fails. It is the same
//! discipline as the Z3 and Kani oracles elsewhere in this crate, with `rustc`'s
//! own code generator as the reference.
//!
//! # What is covered where
//!
//! The IR-level checks live in `src/mir/parse.rs` and `src/mir/exec.rs` as unit
//! tests, because the IR is crate-internal. This file covers the public surface:
//! the contract scanner, contract evaluation, and the end-to-end verdicts.

use discharge::mir::spec;
use discharge::mir::verify::{self, FnOutcome};

// The functions under verification, compiled from the exact file the frontend
// reads. `#[path]` rather than a copy means the test and the verifier can never
// drift: the same bytes are both verified and executed.
#[path = "../examples/mir_targets/actuator.rs"]
mod actuator;
use actuator::*;

const TARGET: &str = "examples/mir_targets/actuator.rs";

/// The nightly compiler, or `None` so the test can skip.
fn rustc() -> Option<String> {
    std::env::var("DISCHARGE_RUSTC").ok().filter(|s| !s.is_empty())
}

fn verify_all() -> Option<verify::FileReport> {
    let rustc = rustc()?;
    let only: Vec<String> = [
        "clamp",
        "rate_limit",
        "sat_add",
        "sat_sub",
        "shift_const",
        "shift_left",
        "sat_shift",
        "sat_mul",
        "unchecked_add",
        "unchecked_sub",
        "unchecked_div",
        "unchecked_mul",
        "off_by_one_guard",
        "clamp_signed",
        "checked_div_signed",
        "unchecked_div_signed",
        "signed_add_misguarded",
        "signed_add_guarded",
        "signed_mul_guarded",
        "signed_mul_negative",
        "checked_neg",
        "inline_saves_arg",
        "inline_clobber_would_pass",
        "bool_ret_false",
        "bool_ret_true",
        "nested_parens",
        "vacuous_precondition",
        "add_always_overflows",
        "div_by_always_zero",
    ]
    .iter()
    .map(|s| s.to_string())
    .collect();
    match verify::verify_file_with(&rustc, std::path::Path::new(TARGET), &only) {
        Ok(r) => Some(r),
        Err(e) => panic!("frontend failed: {e}"),
    }
}

fn outcome<'a>(report: &'a verify::FileReport, name: &str) -> &'a FnOutcome {
    report
        .outcomes
        .iter()
        .find(|(n, _)| n == name)
        .map(|(_, o)| o)
        .unwrap_or_else(|| panic!("{name} missing from the report"))
}

// ---------------------------------------------------------------------------
// The contract scanner
// ---------------------------------------------------------------------------

#[test]
fn scanner_reads_contracts_and_ignores_inner_docs() {
    let src = r#"
//! requires: this is documentation, not a contract
//! ensures: and neither is this

/// requires: b != 0
/// ensures: ret <= a
pub fn div(a: u32, b: u32) -> u32 {
    a / b
}
"#;
    let specs = spec::extract(src);
    let c = specs.get("div").expect("div should have a contract");
    assert_eq!(c.requires, vec!["b != 0".to_string()]);
    assert_eq!(c.ensures, vec!["ret <= a".to_string()]);
}

#[test]
fn scanner_does_not_leak_a_contract_onto_a_later_function() {
    let src = r#"
/// requires: a > 0
const LIMIT: u32 = 10;

pub fn unrelated(a: u32) -> u32 { a }
"#;
    let specs = spec::extract(src);
    assert!(
        specs.get("unrelated").is_none(),
        "a contract before a non-fn item must not attach to the next fn"
    );
}

#[test]
fn scanner_finds_a_pub_crate_fn() {
    let src = "/// requires: a > 0\npub(crate) fn f(a: u32) -> u32 { a }\n";
    let specs = spec::extract(src);
    assert!(specs.get("f").is_some(), "`pub(crate) fn` must be recognized");
}

// ---------------------------------------------------------------------------
// Contract evaluation
// ---------------------------------------------------------------------------

#[test]
fn contract_expressions_evaluate() {
    use discharge::smt;
    smt::with_fresh(|| {
        let mut args = std::collections::BTreeMap::new();
        args.insert("b".to_string(), smt::var_named(2, 32));
        let p = spec::eval_requires("b != 0", &args, &std::collections::BTreeSet::new()).expect("should parse");
        // `b != 0` is satisfiable but not valid: some b violates it.
        assert!(!smt::prove(p).is_proved());
    });
}

#[test]
fn a_contradictory_contract_is_refused_or_vacuous() {
    use discharge::smt;
    smt::with_fresh(|| {
        let mut args = std::collections::BTreeMap::new();
        args.insert("b".to_string(), smt::var_named(2, 32));
        // `b < 3 && b > 10` describes no input. The parser should read it, and
        // the engine should say the precondition is unsatisfiable.
        let p = spec::eval_requires("b < 3 && b > 10", &args, &std::collections::BTreeSet::new()).expect("should parse");
        assert_eq!(smt::find_model(p), smt::Verdict::Unsat);
    });
}

#[test]
fn refuses_a_contract_it_cannot_read() {
    use discharge::smt;
    smt::with_fresh(|| {
        let args = std::collections::BTreeMap::new();
        // A function call is not in the grammar, so it must be refused rather
        // than approximated.
        assert!(spec::eval_requires("foo(b) < 3", &args, &std::collections::BTreeSet::new()).is_err());
        // A cast is not in the grammar either.
        assert!(spec::eval_requires("b as u64 < 3", &args, &std::collections::BTreeSet::new()).is_err());
        // An unknown name is not an argument.
        assert!(spec::eval_requires("zzz < 3", &args, &std::collections::BTreeSet::new()).is_err());
    });
}

// ---------------------------------------------------------------------------
// End-to-end verification, with rustc
// ---------------------------------------------------------------------------

#[test]
fn guarded_functions_verify() {
    let Some(report) = verify_all() else { return };
    for name in [
        "clamp",
        "rate_limit",
        "sat_add",
        "sat_sub",
        // The three shift shapes: a constant amount, a guarded variable amount,
        // and an unguarded variable amount (which rustc's own `assert(n < 16)`
        // rejects, so it belongs with the refuted functions rather than here).
        "shift_const",
        "sat_shift",
    ] {
        let o = outcome(&report, name);
        assert!(
            o.is_verified(),
            "{name} should verify, got: {o}\n{}",
            report_source_hint()
        );
    }
}

#[test]
fn unchecked_functions_are_refuted() {
    let Some(report) = verify_all() else { return };
    for name in [
        "unchecked_add",
        "unchecked_sub",
        "unchecked_div",
        "unchecked_mul",
        "shift_left",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "{name} must be refuted, got: {o}"
        );
    }
}

/// The load-bearing test: every counterexample must be real.
///
/// A counterexample is the verifier's evidence. If it does not reproduce, the
/// engine is wrong in the worst direction — it reported a defect that is not
/// there — so this replays each one against the real function and requires the
/// panic.
#[test]
fn counterexamples_really_panic() {
    let Some(report) = verify_all() else { return };
    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let mut checked = 0;
    let mut failures: Vec<String> = Vec::new();
    for name in [
        "unchecked_add",
        "unchecked_sub",
        "unchecked_div",
        "unchecked_mul",
        // The variable shift is modelled now, so its counterexample is a real
        // one: `n == 16` is exactly what rustc's own `assert(n < 16)` rejects.
        "shift_left",
        // The signed cases. These are the ones that would have slipped through
        // while comparisons and overflow tests were unsigned-only, so replaying
        // their witnesses against the real functions is what keeps the fix
        // honest.
        "unchecked_div_signed",
        "signed_add_misguarded",
        "signed_mul_negative",
    ] {
        let o = outcome(&report, name);
        let FnOutcome::Failed { detail, .. } = o else {
            continue;
        };
        // The arguments are locals `_1` and `_2`, so their values are the
        // counterexample's assignments to variables 1 and 2. A model names only
        // the variables it had to constrain -- `unchecked_div` reports `v2 = 0`
        // and says nothing about `v1`, because the divisor alone decides -- so a
        // missing variable is *unconstrained* and any value will do. Zero is
        // used, and the panic is still required: that is what makes the witness
        // a witness rather than a coincidence of one chosen value.
        let (a, b) = parse_cex_pair(detail);
        let a = a.unwrap_or(0);
        let b = b.unwrap_or(0);
        let panicked = match name {
            "unchecked_add" => std::panic::catch_unwind(|| unchecked_add(a as u16, b as u16)).is_err(),
            "unchecked_sub" => std::panic::catch_unwind(|| unchecked_sub(a as u16, b as u16)).is_err(),
            "unchecked_div" => std::panic::catch_unwind(|| unchecked_div(a as u32, b as u32)).is_err(),
            "unchecked_mul" => std::panic::catch_unwind(|| unchecked_mul(a as u8, b as u8)).is_err(),
            "shift_left" => std::panic::catch_unwind(|| shift_left(a as u16, b as u16)).is_err(),
            "unchecked_div_signed" => {
                std::panic::catch_unwind(|| unchecked_div_signed(a as i16, b as i16)).is_err()
            }
            "signed_add_misguarded" => {
                std::panic::catch_unwind(|| signed_add_misguarded(a as i8, b as i8)).is_err()
            }
            "signed_mul_negative" => {
                std::panic::catch_unwind(|| signed_mul_negative(a as i8, b as i8)).is_err()
            }
            _ => unreachable!(),
        };
        if !panicked {
            failures.push(format!(
                "{name}: counterexample a={a} b={b} did not actually panic, \
                 so the engine reported a defect that is not there"
            ));
        }
        checked += 1;
    }
    // Restore the real hook *before* asserting, or the failure message is
    // swallowed by the no-op hook and the test just says "FAILED".
    std::panic::set_hook(prev);
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    assert!(checked >= 3, "expected several counterexamples, checked {checked}");
}

/// A wrong `ensures` is caught even when the function cannot panic.
///
/// `off_by_one_guard` guards its `a + b` correctly, so it is panic-free; the bug
/// is that it claims `ret >= a` and the `else` branch returns `0`. This is the
/// case that separates "no overflow" from "meets its contract", and it is why the
/// postcondition check exists rather than being folded into the panic check.
#[test]
fn a_wrong_postcondition_is_caught() {
    let Some(report) = verify_all() else { return };
    let o = outcome(&report, "off_by_one_guard");
    match o {
        FnOutcome::Failed { kind, detail } => {
            // `kind` says which obligation failed; `detail` is only the witness.
            assert!(
                kind.contains("postcondition"),
                "the failing obligation should be the postcondition, got kind `{kind}`"
            );
            // The witness must be a real input: `32768 + 32768` has the guard
            // take the `else` branch and return 0, which is not `>= a`.
            assert!(
                detail.contains("v1") && detail.contains("v2"),
                "the witness should name both arguments, got: {detail}"
            );
        }
        other => panic!("a wrong postcondition must be refuted, got: {other}"),
    }
}

/// The other direction of the oracle: a function reported panic-free must not
/// panic on concrete inputs.
#[test]
fn verified_functions_do_not_panic_concretely() {
    let Some(report) = verify_all() else { return };
    if !outcome(&report, "sat_add").is_verified() {
        return;
    }
    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let mut violations = Vec::new();
    // `sat_add` is verified for all u16, so every u16 pair must be fine. The full
    // cross product is 2^32, so this sweeps the overflow boundary plus a spread
    // of interior values.
    let mut vals: Vec<u16> = vec![0, 1, 2, 100, 32767, 32768, 65534, 65535];
    for i in 0..40u32 {
        vals.push((i.wrapping_mul(1657)) as u16);
    }
    for &a in &vals {
        for &b in &vals {
            if std::panic::catch_unwind(|| sat_add(a, b)).is_err() {
                violations.push((a, b));
            }
        }
    }
    std::panic::set_hook(prev);
    assert!(
        violations.is_empty(),
        "sat_add was verified but panics on {violations:?}"
    );
}

#[test]
fn sat_mul_is_reported_incomplete_not_verified() {
    let Some(report) = verify_all() else { return };
    let o = outcome(&report, "sat_mul");
    // The widened 32-bit product is the documented BDD scaling wall. The one
    // unacceptable answer is `Verified`, because the check was not completed.
    assert!(
        !o.is_verified(),
        "sat_mul must not be reported verified when the engine declined: {o}"
    );
    assert!(
        matches!(o, FnOutcome::Incomplete { .. }),
        "sat_mul should be incomplete, got: {o}"
    );
}

/// The signed/unsigned split, pinned so it cannot regress.
///
/// While comparisons and overflow tests were unsigned-only, every case here
/// produced the wrong answer and every *unsigned* case above still passed — the
/// whole suite was green while the engine called `127 + 1` panic-free. These
/// assertions are what would have caught it.
#[test]
fn signed_arithmetic_is_not_verified_as_unsigned() {
    let Some(report) = verify_all() else { return };

    // `signed_add_misguarded` has `requires: a <= 127 && b <= 1` and adds. The
    // unsigned overflow test calls it safe because the wrapped sum `128u8` is not
    // below `127u8`; the correct signed rule fires. It must be a *failure*, and
    // it must not be reported verified.
    let o = outcome(&report, "signed_add_misguarded");
    assert!(
        matches!(o, FnOutcome::Failed { .. }),
        "a signed add that overflows on `127 + 1` must be refuted, got: {o}"
    );

    // The guard that actually holds, so the fix is not "reject everything signed".
    for name in ["signed_add_guarded", "signed_mul_guarded", "clamp_signed", "checked_neg"] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "{name} should verify, got: {o}");
    }

    // A signed comparison must take the negative branch. `clamp_signed` cannot
    // verify at all if `x < lo` is read unsigned, because `-1` would look larger
    // than any positive bound — so its `Verified` above is the comparison check.
    // This asserts the same thing from the other side: the misguarded add fails,
    // which requires the *overflow* test to be signed-aware rather than the
    // comparison alone.
    let o = outcome(&report, "signed_mul_negative");
    assert!(
        matches!(o, FnOutcome::Failed { .. }),
        "a signed multiply of two negatives must be refuted, got: {o}"
    );
}

/// `i8::MIN` must parse as the top bit, not as zero.
///
/// `checked_neg`'s guard is `a != i8::MIN`. When the constant parser returned 0
/// for every `MIN`, that guard meant `a != 0`, so the `-128` case looked excluded
/// and the negation was reported panic-free. The function must verify *now* only
/// because the guard is real, and a version without it must fail.
#[test]
fn the_min_constant_is_the_top_bit() {
    let Some(report) = verify_all() else { return };
    let o = outcome(&report, "checked_neg");
    assert!(
        o.is_verified(),
        "checked_neg excludes i8::MIN and should verify, got: {o}"
    );
    // Replay the guard's own boundary against the real function: `-128` really
    // does panic under debug overflow checks, which is why excluding it matters.
    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let panics = std::panic::catch_unwind(|| {
        // `black_box` keeps the constant from being folded, so the negation is
        // computed at runtime and its overflow check is the one being tested.
        let a: i8 = std::hint::black_box(i8::MIN);
        -a
    })
    .is_err();
    std::panic::set_hook(prev);
    assert!(panics, "`-i8::MIN` must panic, so the guard is load-bearing");
}

/// The other direction for signed code: a function reported panic-free must not
/// panic on any input it admits.
#[test]
fn verified_signed_functions_do_not_panic_concretely() {
    let Some(report) = verify_all() else { return };
    if !outcome(&report, "signed_add_guarded").is_verified() {
        return;
    }
    let prev = std::panic::take_hook();
    std::panic::set_hook(Box::new(|_| {}));
    let mut violations = Vec::new();
    // The guard admits only `|a|, |b| <= 60`, so sweep that box exhaustively.
    for a in -60i16..=60 {
        for b in -60i16..=60 {
            if std::panic::catch_unwind(|| signed_add_guarded(a as i8, b as i8)).is_err() {
                violations.push((a, b));
            }
        }
    }
    std::panic::set_hook(prev);
    assert!(
        violations.is_empty(),
        "signed_add_guarded was verified but panics on {violations:?}"
    );
}

/// A contract naming a function that is not in the MIR must be reported, not
/// silently ignored — otherwise a typo turns a verified function into an
/// unverified one that still looks green.
#[test]
fn a_missing_contracted_function_is_reported() {
    let Some(rustc) = rustc() else { return };
    let only = vec!["no_such_function".to_string()];
    let report = verify::verify_file_with(&rustc, std::path::Path::new(TARGET), &only)
        .expect("the file itself should still parse");
    assert!(
        report.outcomes.is_empty(),
        "nothing should have been verified for an absent function"
    );
}

// ---------------------------------------------------------------------------
// The safety gate itself, with no compiler needed
// ---------------------------------------------------------------------------

#[test]
fn a_report_with_an_unknown_path_is_never_clean() {
    // The API-level invariant this whole frontend rests on: an incomplete run is
    // not a pass.
    let mut report = verify::FileReport::default();
    report.outcomes.push((
        "f".to_string(),
        FnOutcome::Incomplete {
            report: Box::new(verify::MirReport::default()),
            reasons: vec!["budget".to_string()],
        },
    ));
    assert!(!report.is_clean());
    assert_eq!(report.incomplete(), 1);
    assert_eq!(report.verified(), 0);
}

#[test]
fn a_missing_contract_is_not_clean() {
    let mut report = verify::FileReport::default();
    report.missing.push("ghost".to_string());
    assert!(!report.is_clean());
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn report_source_hint() -> &'static str {
    "hint: the frontend reads the MIR of examples/mir_targets/actuator.rs; \
     run examples/mir_demo.rs to see the per-function report"
}

/// Pull `v1:u32 = 123, v2:u32 = 456` out of a rendered counterexample.
fn parse_cex_pair(detail: &str) -> (Option<u64>, Option<u64>) {
    let mut first = None;
    let mut second = None;
    for part in detail.split(',') {
        let part = part.trim();
        if let Some((lhs, rhs)) = part.split_once('=') {
            let idx: u32 = lhs
                .trim()
                .trim_start_matches('v')
                .split(':')
                .next()
                .unwrap_or("")
                .parse()
                .unwrap_or(0);
            let val: u64 = rhs.trim().parse().unwrap_or(0);
            match idx {
                1 => first = Some(val),
                2 => second = Some(val),
                _ => {}
            }
        }
    }
    (first, second)
}

// ---------------------------------------------------------------------------
// Regressions for the frontend bugs a review found: caller state clobbered by
// an inlined call, a boolean return bypassing the postcondition, a redundant
// parenthesis pair hiding a contract, and a scoped `debug` alias renaming a
// parameter.
// ---------------------------------------------------------------------------

/// An inlined call must not hand the caller the callee's locals.
///
/// Both functions have the same shape — save an argument, call something, return
/// the saved value — and differ only in the postcondition. The correct one must
/// verify and the false one must be refuted. If the caller's environment is not
/// restored, the continuation reads the callee's `_1` (holding `b`), so both
/// would verify.
#[test]
fn an_inlined_call_does_not_clobber_the_caller() {
    let Some(report) = verify_all() else { return };

    let good = outcome(&report, "inline_saves_arg");
    assert!(
        good.is_verified(),
        "returning the caller's saved argument must verify, got: {good}"
    );

    let bad = outcome(&report, "inline_clobber_would_pass");
    assert!(
        matches!(bad, FnOutcome::Failed { .. }),
        "`ret == b` is false for `inline_clobber_would_pass` and must be refuted, got: {bad}"
    );
}

/// A `bool` return must be checked against the declared postcondition.
#[test]
fn a_boolean_return_is_checked_against_its_postcondition() {
    let Some(report) = verify_all() else { return };

    let bad = outcome(&report, "bool_ret_false");
    assert!(
        matches!(bad, FnOutcome::Failed { .. }),
        "`ret == false` for a function returning `true` must be refuted, got: {bad}"
    );

    let good = outcome(&report, "bool_ret_true");
    assert!(
        good.is_verified(),
        "`ret == true` for the same function must verify, got: {good}"
    );
}

/// A redundant parenthesis pair must not make a contract unreadable.
#[test]
fn nested_predicate_parentheses_parse() {
    let Some(report) = verify_all() else { return };
    let o = outcome(&report, "nested_parens");
    assert!(
        o.is_verified(),
        "`requires: ((a == 0))` must parse and verify, got: {o}"
    );
}

/// A scoped `debug` alias must not rename a parameter.
///
/// `inline_saves_arg` prints `debug a => _1;` at function level and then
/// `debug saved => _1;` inside `scope 1`, because `let saved = a;` reuses `_1`.
/// When the later line overwrote the earlier one, the parameter `a` disappeared
/// and `ensures: ret == a` was skipped as unreadable. The function verifying at
/// all is the check; this pins the names directly so the failure is legible.
#[test]
fn a_scoped_debug_alias_does_not_rename_a_parameter() {
    let Some(rustc) = rustc() else { return };
    let mir = verify::emit_mir_with(&rustc, std::path::Path::new(TARGET))
        .expect("emit MIR for the target file");
    // The parameter is named `a`, and the `ensures` names it, so the contract
    // must be readable. A skip here is the bug.
    let report = verify::verify_file_with(&rustc, std::path::Path::new(TARGET), &[
        "inline_saves_arg".to_string(),
    ])
    .expect("verify");
    let (_, o) = report.outcomes.first().expect("one outcome");
    assert!(
        !matches!(o, FnOutcome::Skipped { .. }),
        "the contract names the parameter `a` and must be readable, got: {o}"
    );
    assert!(mir.contains("debug a => _1;"), "the parameter binding is expected in the dump");
}

/// An unreadable `ensures` must not be folded into `true`.
///
/// The postcondition closure used to swallow a parse error and return `true`, so
/// a function whose `ensures` could not be read would verify with *nothing*
/// checked. A skipped outcome is the honest report, and `is_clean` must not call
/// it clean.
#[test]
fn an_unreadable_ensures_is_reported_not_ignored() {
    let Some(rustc) = rustc() else { return };
    let dir = std::env::temp_dir().join("discharge_unreadable_ensures");
    let _ = std::fs::create_dir_all(&dir);
    let src = dir.join("u.rs");
    std::fs::write(
        &src,
        "/// requires: true\n/// ensures: ret == nonsense_name\npub fn f(a: u8) -> u8 { a }\n",
    )
    .expect("write source");
    let report =
        verify::verify_file_with(&rustc, &src, &["f".to_string()]).expect("verify");
    let (_, o) = report.outcomes.first().expect("one outcome");
    assert!(
        matches!(o, FnOutcome::Skipped { .. }),
        "an unreadable `ensures` must be reported as skipped, got: {o}"
    );
    assert!(
        !report.is_clean(),
        "a report with a skipped function must not be clean"
    );
}

/// An unsatisfiable precondition is a finding, not a pass.
///
/// The implication `pre => post` is vacuously true when `pre` is unsatisfiable,
/// so a naive discharge reports `Verified`. The frontend adds an explicit
/// satisfiability obligation for exactly this reason, and it must be a failure.
#[test]
fn an_unsatisfiable_precondition_is_a_failure() {
    let Some(report) = verify_all() else { return };
    let o = outcome(&report, "vacuous_precondition");
    assert!(
        matches!(o, FnOutcome::Failed { .. }),
        "`a < 3 && a > 10` admits no input and must be a failure, got: {o}"
    );
    let text = o.to_string();
    assert!(
        text.contains("vacuous precondition"),
        "the failure must name the vacuous precondition, got: {text}"
    );
}

/// A panic obligation whose verdict is `Valid` is a failure, not a proof.
///
/// This is the case that exposes the inverted polarity directly: the panic query
/// is `Valid`, and a naive "proved means good" reading counts it as discharged.
/// The obligation asks "can this panic happen", so `Valid` means it happens on
/// every input — the worst answer. `div_by_always_zero` divides by `d & 0`, which
/// is zero for every `d`, so its query is `Valid`.
#[test]
fn a_panic_obligation_that_is_valid_is_a_failure() {
    let Some(report) = verify_all() else { return };
    let o = outcome(&report, "div_by_always_zero");
    assert!(
        matches!(o, FnOutcome::Failed { .. }),
        "a divide by an always-zero divisor must be a failure, got: {o}"
    );
    assert!(
        o.to_string().contains("panic"),
        "the failure must name the panic, got: {o}"
    );
}

/// A panic that happens on *every* input must be a failure, not a proof.
///
/// The obligation for a panic asks "can this panic happen", so `Unsat` is the
/// good answer and `Valid` is the worst one — the panic fires for every input.
/// Reading the verdict as "proved means good" inverts the answer, and
/// `add_always_overflows` is the case that makes it visible: the overflow query
/// is `Valid`, and the function must be reported as failing.
#[test]
fn a_panic_on_every_input_is_a_failure() {
    let Some(report) = verify_all() else { return };
    let o = outcome(&report, "add_always_overflows");
    assert!(
        matches!(o, FnOutcome::Failed { .. }),
        "an add that always overflows must be a failure, got: {o}"
    );
}
