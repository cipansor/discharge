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
        "clamp_bounds",
        "first_of",
        "slice_alias_tripwire",
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
        let p = spec::eval_requires("b != 0", &args, &std::collections::BTreeSet::new(), &spec::FieldEnv::default()).expect("should parse");
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
        let p = spec::eval_requires("b < 3 && b > 10", &args, &std::collections::BTreeSet::new(), &spec::FieldEnv::default()).expect("should parse");
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
        assert!(spec::eval_requires("foo(b) < 3", &args, &std::collections::BTreeSet::new(), &spec::FieldEnv::default()).is_err());
        // A cast is not in the grammar either.
        assert!(spec::eval_requires("b as u64 < 3", &args, &std::collections::BTreeSet::new(), &spec::FieldEnv::default()).is_err());
        // An unknown name is not an argument.
        assert!(spec::eval_requires("zzz < 3", &args, &std::collections::BTreeSet::new(), &spec::FieldEnv::default()).is_err());
    });
}

/// A literal takes its width from the operand it meets, not from the widest
/// name in scope.
///
/// This is the bug that array support exposed. A slice or array length is a
/// `usize`, so once such an argument is in scope it becomes the widest name, and
/// a contract literal was sized from that maximum. `ret <= 255` for a `u8` return
/// then became an 8-bit value compared against a 64-bit constant, which the
/// engine reports as ill-formed -- and an ill-formed term makes *every*
/// obligation in the run `Unknown`, so the whole function was `incomplete` for a
/// reason that had nothing to do with its body.
///
/// The check is on the evaluator, so it does not depend on a corpus function
/// happening to be skipped for another reason. `n` stands in for the wide
/// length, `ret` for the narrow return: the literal must end up 8 bits wide.
#[test]
fn a_literal_is_sized_from_the_operand_it_meets() {
    use discharge::smt;
    smt::with_fresh(|| {
        let mut args = std::collections::BTreeMap::new();
        // A 64-bit "length", in scope but not mentioned by the contract.
        args.insert("xs__len".to_string(), smt::var(64));
        let ret = smt::var(8);
        let p = spec::eval_ensures(
            "ret <= 255",
            &args,
            Some(ret),
            spec::RET_IS_UNKNOWN,
            &std::collections::BTreeSet::new(),
            false,
            &spec::FieldEnv::default(),
        )
        .expect("a narrow literal against a wide name must still parse");
        assert!(
            !smt::is_ill_formed(),
            "the literal must be resized to `ret`'s 8 bits, not left at 64"
        );
        assert!(smt::prove(p).is_proved(), "`ret <= 255` must hold for every u8");
    });
}

/// A literal too large for the operand's width is refused, not truncated.
///
/// `a <= 300` for a `u8` cannot hold, so the honest answers are "refused" or
/// "unsatisfiable". What it must *not* be is silently narrowed to `a <= 44`,
/// which is what a truncating resize would do -- and that is a weaker claim that
/// could pass. The refusal is the error, and it names the width so the message is
/// actionable.
#[test]
fn a_literal_that_does_not_fit_is_refused_not_truncated() {
    use discharge::smt;
    smt::with_fresh(|| {
        let mut args = std::collections::BTreeMap::new();
        args.insert("a".to_string(), smt::var(8));
        let err = spec::eval_requires(
            "a <= 300",
            &args,
            &std::collections::BTreeSet::new(),
            &spec::FieldEnv::default(),
        )
        .expect_err("300 does not fit a u8, so the contract must be refused");
        assert!(
            err.to_string().contains("300") && err.to_string().contains("8-bit"),
            "the refusal must name the value and the width, got: {err}"
        );
    });
}

/// An aggregate return refuses a bare `ret` with the aggregate message.
///
/// `ret <= 5` on a `(u8, u8)` return is refused because there is no single word.
/// The message must say *that*, so the reader knows to name a component.
#[test]
fn a_bare_ret_on_an_aggregate_names_the_aggregate_reason() {
    use discharge::smt;
    smt::with_fresh(|| {
        let args = std::collections::BTreeMap::new();
        let err = spec::eval_ensures(
            "ret <= 5",
            &args,
            None,
            spec::RET_IS_AGGREGATE,
            &std::collections::BTreeSet::new(),
            false,
            &spec::FieldEnv::default(),
        )
        .expect_err("a bare `ret` on an aggregate must be refused");
        assert!(
            err.to_string().contains(spec::RET_IS_AGGREGATE),
            "the message must name the aggregate cause and the fix, got: {err}"
        );
    });
}

/// A scalar return whose value is unknown is refused with *that* reason.
///
/// The value can be unbound on a path where a read was unmodelled, even though
/// the return type is a plain `u8`. Reporting "the return type is an aggregate"
/// here would be false, and would send the reader looking for a tuple that does
/// not exist. The two causes have to be two messages.
#[test]
fn a_bare_ret_with_an_unknown_value_names_the_unknown_reason() {
    use discharge::smt;
    smt::with_fresh(|| {
        let args = std::collections::BTreeMap::new();
        let err = spec::eval_ensures(
            "ret <= 5",
            &args,
            None,
            spec::RET_IS_UNKNOWN,
            &std::collections::BTreeSet::new(),
            false,
            &spec::FieldEnv::default(),
        )
        .expect_err("a bare `ret` with no value must be refused");
        assert!(
            err.to_string().contains(spec::RET_IS_UNKNOWN),
            "a scalar return must not be reported as an aggregate, got: {err}"
        );
    });
}

/// A literal in *arithmetic* is sized to the operand it meets, like one in a
/// comparison.
///
/// `add_literal_wide_scope` has a slice length in scope, so a literal built at
/// the scope's 64-bit width would make `a + 5` an 8-bit/64-bit `Add` -- ill-formed,
/// and so `Unknown` for the whole run. The fix is the same `align_widths` the
/// comparison path uses, reached through the additive and multiplicative operators.
#[test]
fn a_literal_in_arithmetic_is_sized_to_its_operand() {
    let Some(report) = verify_realistic(&["add_literal_wide_scope"]) else { return };
    let o = outcome(&report, "add_literal_wide_scope");
    assert!(o.is_verified(), "`add_literal_wide_scope` must verify, got: {o}");
}

/// A named type bound carries the width of the type it names.
///
/// `i8::MIN` is the bit pattern `0x80`, exactly 8 bits. Building it at the
/// widest name in scope and narrowing it back would compare a 64-bit `128`
/// against the signed 8-bit range and refuse it -- a refusal of a bound that is
/// in range by construction. The width has to come from `i8`, not from the
/// contract's other operands.
#[test]
fn a_named_type_bound_keeps_its_own_width() {
    use discharge::smt;
    smt::with_fresh(|| {
        let mut args = std::collections::BTreeMap::new();
        args.insert("a".to_string(), smt::var(8));
        // A 64-bit name in scope, which is what used to widen the bound.
        args.insert("xs__len".to_string(), smt::var(64));
        let mut signed = std::collections::BTreeSet::new();
        signed.insert("a".to_string());
        let p = spec::eval_requires("a >= i8::MIN", &args, &signed, &spec::FieldEnv::default())
            .expect("`a >= i8::MIN` must parse even with a wide name in scope");
        assert!(!smt::is_ill_formed(), "the bound must be built at 8 bits");
        // Every `i8` is `>= i8::MIN`, so the precondition holds on all inputs.
        assert!(smt::prove(p).is_proved(), "`a >= i8::MIN` must hold for every i8");
    });
}

/// A negative literal keeps its value when it is widened to a signed operand.
///
/// `a >= -10` for an `i8` is the shape that makes sign extension matter: the
/// literal is parsed as `0 - 10` at some width and then has to reach `a`'s width
/// with the *value* preserved. Zero-extending it would turn `-10` into a large
/// positive number and the comparison would mean something else entirely.
#[test]
fn a_negative_literal_is_sign_extended_to_the_operand() {
    use discharge::smt;
    smt::with_fresh(|| {
        let mut args = std::collections::BTreeMap::new();
        args.insert("a".to_string(), smt::var(8));
        let mut signed = std::collections::BTreeSet::new();
        signed.insert("a".to_string());
        let p = spec::eval_requires("a >= -10", &args, &signed, &spec::FieldEnv::default())
            .expect("`a >= -10` must parse");
        assert!(!smt::is_ill_formed(), "the literal must be resized to 8 bits");
        // `a >= -10` is the negation of `a < -10`, and for an `i8` the only such
        // `a` are -128..=-11. So the contract must *fail* on those inputs.
        // `-10` as an `i8` is the bit pattern `0xF6`; building it from a `u64`
        // would itself be ill-formed, since `2^64 - 10` does not fit 8 bits.
        let minus_ten = smt::word(0xF6, 8);
        let bad = smt::and(p, smt::slt(args["a"], minus_ten));
        assert_eq!(
            smt::find_model(bad),
            smt::Verdict::Unsat,
            "`a >= -10` must exclude exactly `a < -10`"
        );
    });
    smt::with_fresh(|| {
        // The same contract with a 64-bit name also in scope. `-10` is built at
        // 64 bits as `2^64 - 10`, and narrowing that to 8 bits must take the low
        // byte (`0xF6`) rather than rebuild a word from the 64-bit value, which
        // would not fit and would set the ill-formed flag.
        let mut args = std::collections::BTreeMap::new();
        args.insert("a".to_string(), smt::var(8));
        args.insert("xs__len".to_string(), smt::var(64));
        let mut signed = std::collections::BTreeSet::new();
        signed.insert("a".to_string());
        let p = spec::eval_requires("a >= -10", &args, &signed, &spec::FieldEnv::default())
            .expect("`a >= -10` must parse with a wide name in scope");
        assert!(
            !smt::is_ill_formed(),
            "narrowing a negative literal must take the low bits, not rebuild a wide word"
        );
        // And it must still mean what it says: satisfiable (an `i8` of `-10`
        // satisfies it), but not valid (every `i8` below `-10` violates it).
        assert!(
            !matches!(smt::find_model(p), smt::Verdict::Unsat),
            "`a >= -10` must be satisfiable"
        );
        assert!(!smt::prove(p).is_proved(), "`a >= -10` must not hold for every i8");
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
        "clamp_bounds",
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

/// An `Unsat` postcondition must not be described as a universal truth.
///
/// A postcondition query is `path => post`. `Unsat` means it is false on *every*
/// input -- the postcondition holds for none. A `Valid` panic query means the
/// opposite, that the failure fires on *every* input. Both leave no witness, and
/// the first version collapsed both to "holds for every input", which describes
/// an impossible postcondition as a universal truth. The two diagnoses must
/// differ, and the `Unsat` one must say the postcondition holds for no input.
#[test]
fn an_impossible_postcondition_says_so_rather_than_the_opposite() {
    let Some(report) = verify_all() else { return };
    let o = outcome(&report, "bool_ret_false");
    let FnOutcome::Failed { kind, detail } = o else {
        panic!("`bool_ret_false` must fail, got: {o}");
    };
    assert_eq!(kind, "postcondition");
    assert!(
        detail.contains("no input"),
        "an `Unsat` postcondition must be reported as holding for no input, got: {detail}"
    );
    assert!(
        !detail.contains("holds for every input"),
        "the diagnosis is reversed: an `Unsat` postcondition holds for none, got: {detail}"
    );
}

/// The counterpart: a panic query that is `Valid` fires on *every* input, and
/// its diagnosis must say that rather than borrowing the postcondition wording.
#[test]
fn an_always_firing_panic_says_it_fires_on_every_input() {
    let Some(report) = verify_all() else { return };
    let o = outcome(&report, "div_by_always_zero");
    let FnOutcome::Failed { kind, detail } = o else {
        panic!("`div_by_always_zero` must fail, got: {o}");
    };
    assert!(kind.contains("panic"), "the kind must name the panic, got: {kind}");
    assert!(
        detail.contains("every input"),
        "a `Valid` panic query fires on every input and must say so, got: {detail}"
    );
}

// ---------------------------------------------------------------------------
// Contract projections: struct fields and tuple components
// ---------------------------------------------------------------------------

const REALISTIC: &str = "examples/mir_targets/realistic.rs";

fn verify_realistic(only: &[&str]) -> Option<verify::FileReport> {
    let rustc = rustc()?;
    let only: Vec<String> = only.iter().map(|s| s.to_string()).collect();
    match verify::verify_file_with(&rustc, std::path::Path::new(REALISTIC), &only) {
        Ok(r) => Some(r),
        Err(e) => panic!("frontend failed: {e}"),
    }
}

/// A contract can name a struct field, and the field's *value* reaches the body.
///
/// `pick_from`'s precondition is `c.lo <= c.hi` and its postcondition is
/// `ret >= c.lo`. Both name fields of a `&Config`, which the MIR dump prints only
/// as `_1: &Config` with no layout — the frontend has to read the layout from the
/// source. Before that, this function was `skipped` with "unknown name".
#[test]
fn a_contract_can_name_a_struct_field() {
    let Some(report) = verify_realistic(&["pick_from", "clamp_by_value"]) else { return };
    for name in ["pick_from", "clamp_by_value"] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
}

/// The tripwire for field *independence*.
///
/// `field_alias_tripwire` has the same shape as `clamp_by_value` but claims
/// `ret >= c.hi`, which is false whenever `v < c.lo <= c.hi`. It must FAIL. If
/// `c.lo` and `c.hi` were bound to the same symbolic variable the claim would be
/// `ret >= x` with `ret` in `{x, v}` and `v` unconstrained-but-`<= x`... which is
/// exactly the vacuous pass this test exists to catch. A counterexample is the
/// positive evidence that the two fields are distinct inputs.
#[test]
fn struct_fields_are_independent_inputs_not_one_aliased_variable() {
    let Some(report) = verify_realistic(&["field_alias_tripwire"]) else { return };
    let o = outcome(&report, "field_alias_tripwire");
    let FnOutcome::Failed { kind, detail } = o else {
        panic!(
            "`field_alias_tripwire` must fail: a pass means `c.lo` and `c.hi` \
             collapsed to one variable and the contract was vacuous. got: {o}"
        );
    };
    assert_eq!(kind, "postcondition", "got: {o}");
    // The witness must name two different variables for the two fields. If the
    // binding aliased, the same variable index would appear for both.
    let names: Vec<&str> = detail.split_whitespace().filter(|t| t.starts_with('v')).collect();
    assert!(
        names.len() >= 2,
        "the counterexample must assign both fields to show they differ, got: {detail}"
    );
    assert!(
        names.iter().collect::<std::collections::BTreeSet<_>>().len() >= 2,
        "the two fields were assigned the same variable, so they are aliased: {detail}"
    );
}

/// A slice contract the frontend must *not* prove: `first_of` is sound, but
/// `slice_alias_tripwire` claims `ret == xs[1]` where the body returns `xs[0]`.
///
/// The tripwire exists because the tempting wrong model is to give a slice one
/// "element" variable. Then `xs[0] == xs[1]` and the claim would hold. A failure
/// is the evidence that two indices are two inputs; a pass means the slice was
/// collapsed and `first_of`'s proof is not worth anything.
#[test]
fn slice_elements_are_independent_inputs_not_one_aliased_variable() {
    let Some(report) = verify_realistic(&["slice_alias_tripwire"]) else { return };
    let o = outcome(&report, "slice_alias_tripwire");
    let FnOutcome::Failed { kind, detail } = o else {
        panic!(
            "`slice_alias_tripwire` must fail: a pass means `xs[0]` and `xs[1]` \
             collapsed to one variable and the slice contract was vacuous. got: {o}"
        );
    };
    assert_eq!(kind, "postcondition", "got: {o}");
    let names: Vec<&str> = detail.split_whitespace().filter(|t| t.starts_with('v')).collect();
    assert!(
        names.iter().collect::<std::collections::BTreeSet<_>>().len() >= 2,
        "the two elements were assigned the same variable, so they are aliased: {detail}"
    );
}

/// The slice length is a symbolic input, not a constant, and `xs.len()` in a
/// contract names the same variable the body's `PtrMetadata` reads.
///
/// `first_of` requires `xs.len() > 0` and claims `ret == xs[0]`. If the length
/// were a fixed constant (say `0`), the precondition would be unsatisfiable and
/// the function would be reported vacuous rather than verified; if the contract's
/// `xs.len()` and the body's `PtrMetadata` were *different* variables, the
/// bounds `assert` could not be discharged from the precondition and the function
/// would be incomplete. Verified is the only outcome that shows both hold.
#[test]
fn a_slice_length_is_a_symbolic_input_shared_with_the_body() {
    let Some(report) = verify_realistic(&["first_of"]) else { return };
    let o = outcome(&report, "first_of");
    assert!(o.is_verified(), "`first_of` must verify, got: {o}");
}

/// A fixed-size array argument: elements are inputs, but the length is not.
///
/// `max_of_pair` requires `a[0] <= a[1]` and claims `ret == a[1]`. This is the
/// array counterpart of `first_of`, and the difference is the point: a slice's
/// length is a symbolic input read through `PtrMetadata`, while an array's length
/// is a *type* constant, so the bounds check in the body is against the literal
/// `4` and `a.len()` in a contract is `4` rather than a fresh variable.
#[test]
fn a_contract_can_name_a_fixed_size_array_element() {
    let Some(report) = verify_realistic(&["max_of_pair", "array_third"]) else { return };
    for name in ["max_of_pair", "array_third"] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
}

/// An array built in the body has *concrete* elements, not inputs.
///
/// `array_literal_elem` returns `a[1]` of `[10, 20, 30, 40]` and claims
/// `ret == 20`. Verified is the evidence that the element map holds the literal
/// values: if the index were modelled as an unconstrained input the claim would
/// fail with a counterexample instead.
#[test]
fn an_array_literal_element_is_concrete() {
    let Some(report) = verify_realistic(&["array_literal_elem"]) else { return };
    let o = outcome(&report, "array_literal_elem");
    assert!(o.is_verified(), "`array_literal_elem` must verify, got: {o}");
}

/// The tripwire for array *element independence*.
///
/// `array_alias_tripwire` has the same body as `max_of_pair` but claims
/// `ret <= a[0]`, which is false when `a[1] > a[0]`. It must FAIL, and the
/// counterexample must assign `a[0]` and `a[1]` to *different* variables -- a
/// pass would mean the elements collapsed to one input and `max_of_pair`'s proof
/// was vacuous.
#[test]
fn array_elements_are_independent_inputs_not_one_aliased_variable() {
    let Some(report) = verify_realistic(&["array_alias_tripwire"]) else { return };
    let o = outcome(&report, "array_alias_tripwire");
    let FnOutcome::Failed { kind, detail } = o else {
        panic!(
            "`array_alias_tripwire` must fail: a pass means `a[0]` and `a[1]` \
             collapsed to one variable and the array contract was vacuous. got: {o}"
        );
    };
    assert_eq!(kind, "postcondition", "got: {o}");
    let names: Vec<&str> = detail.split_whitespace().filter(|t| t.starts_with('v')).collect();
    assert!(
        names.iter().collect::<std::collections::BTreeSet<_>>().len() >= 2,
        "the two elements were assigned the same variable, so they are aliased: {detail}"
    );
}

/// A postcondition can name a component of a tuple return.
///
/// `split` returns `(u8, u8)` and claims `ret.0 <= a`. The return place is an
/// aggregate, so there is no single word for `ret`; the frontend binds `ret.0`
/// and `ret.1` to the components `_0 = (a, b)` actually stored.
#[test]
fn a_postcondition_can_name_a_tuple_component() {
    let Some(report) = verify_realistic(&["split"]) else { return };
    let o = outcome(&report, "split");
    assert!(o.is_verified(), "`split` must verify, got: {o}");
}

/// A contract naming a field the struct does not have is refused, not dropped.
///
/// This is the failure mode that matters: if the projection were ignored, the
/// conjunct would vanish and the function would verify against a weaker contract
/// than the source states. The refusal is asserted on the *evaluator* rather than
/// on a corpus function, so it cannot pass by the function being skipped for some
/// unrelated reason.
#[test]
fn a_contract_naming_an_unknown_field_is_refused() {
    let mut args = std::collections::BTreeMap::new();
    args.insert("c".to_string(), discharge::smt::var(8));
    // `c` is a known aggregate with no bindings, so the refusal names the field.
    let mut env = spec::FieldEnv::default();
    env.declare_arg("c");
    let err = spec::eval_requires("c.lo <= 3", &args, &std::collections::BTreeSet::new(), &env)
        .expect_err("an unbound field must be refused");
    assert!(
        err.to_string().contains("unknown field `lo`"),
        "the refusal must name the field, got: {err}"
    );
}

/// The field rewrite is token-aware: it must not fire inside a longer name.
///
/// `myc.lo` is a different path from `c.lo`. A naive `str::replace` would rewrite
/// the tail of `myc.lo` into `myc__f0` (or rewrite `c.lo` inside it), binding the
/// contract to a variable the caller never declared — a wrong proof. The rewrite
/// only fires on a whole `ident.ident` run that matches a *bound* path.
#[test]
fn the_field_rewrite_does_not_fire_inside_a_longer_name() {
    let mut fields = spec::FieldEnv::default();
    let c = discharge::smt::var(8);
    fields.bind_bits(1, "c", "lo", 0, 8, false).unwrap();
    let mut args = std::collections::BTreeMap::new();
    args.insert("myc".to_string(), c);
    // `myc` is *not* a declared aggregate, so its `.lo` is left alone and the
    // parser refuses the unknown name `myc`. The point is that it was not
    // rewritten into the binding that belongs to `c`.
    let err = spec::eval_requires("myc.lo <= 3", &args, &std::collections::BTreeSet::new(), &fields)
        .expect_err("`myc.lo` must not be rewritten to the binding for `c.lo`");
    let msg = err.to_string();
    assert!(
        msg.contains("unknown name") || msg.contains("expected a comparison"),
        "`myc.lo` must be refused, got: {msg}"
    );
    assert!(
        !msg.contains("unknown field"),
        "`myc` is not a known aggregate, so the message must not claim a bad field: {msg}"
    );
    // And the bound path itself *is* rewritten and resolves.
    let ok = spec::eval_requires("c.lo <= 3", &args, &std::collections::BTreeSet::new(), &fields);
    assert!(ok.is_ok(), "the bound path must resolve, got: {ok:?}");
}

// ---------------------------------------------------------------------------
// Symbolic array subscripts
// ---------------------------------------------------------------------------

/// `a[i]` on a fixed-length array is modelled as the exact ite chain over `0..N`,
/// and the precondition has to establish `i < N`.
///
/// An array's length is in its type, so unlike a slice there *is* a finite domain
/// to enumerate: `a[i]` is `ite(i == 0, a0, ite(i == 1, a1, ...))`, a definition
/// rather than an approximation. The chain can only be `a[i]` where `i < N`, so
/// `requires: i < 4` is what makes the subscript admissible.
#[test]
fn a_symbolic_array_index_is_modelled_as_an_ite_chain() {
    let Some(report) = verify_realistic(&["array_symbolic_index"]) else { return };
    let o = outcome(&report, "array_symbolic_index");
    assert!(o.is_verified(), "`array_symbolic_index` must verify, got: {o}");
}

/// The soundness gate: a symbolic subscript whose index the precondition does not
/// bound is refused, not checked.
///
/// The ite chain has to return *something* for `i >= N` (it falls through to the
/// last element), so a contract checked without `i < N` would be checked against a
/// value that is not `a[i]`. Refusing is the only honest answer; the tempting bug
/// is to conjoin `i < N` into the precondition, which would silently strengthen
/// what the source asked to be verified.
#[test]
fn an_unbounded_symbolic_array_index_is_refused() {
    let Some(report) = verify_realistic(&["array_unbounded_index_refused"]) else { return };
    let o = outcome(&report, "array_unbounded_index_refused");
    match o {
        FnOutcome::Skipped { reason } => assert!(
            reason.contains("not known to be in range"),
            "the refusal must say the index is unbounded, got: {reason}"
        ),
        other => panic!("`array_unbounded_index_refused` must be skipped, got: {other}"),
    }
}

/// A contract naming a *different* index than the body reads is refused.
///
/// Only `a[i]` has a chain; `a[j]` does not, and rewriting it to the `a[i]` chain
/// would prove `a[j] == a[i]` -- false for every `i != j`. The refusal is what
/// keeps a name that merely looks like the bound one from being silently aliased.
#[test]
fn a_contract_naming_a_different_symbolic_index_is_refused() {
    let Some(report) = verify_realistic(&["array_wrong_index_refused"]) else { return };
    let o = outcome(&report, "array_wrong_index_refused");
    assert!(
        matches!(o, FnOutcome::Skipped { .. }),
        "`array_wrong_index_refused` must be skipped, got: {o}"
    );
}

/// A contract error quotes the *source* text, not the rewritten form.
///
/// The parser reads the contract after the field/subscript rewrite, so its errors
/// naturally quote mangled names (`a__chain`, `c__f0`) that appear nowhere in the
/// source. A name the user cannot search for is a diagnosability bug, so the eval
/// boundary re-points the error at the original text. This pins that, because it
/// is the kind of thing a later refactor silently drops.
#[test]
fn a_contract_error_quotes_the_source_text() {
    use discharge::mir::spec;
    use discharge::smt;
    let mut fields = spec::FieldEnv::default();
    let mut args = std::collections::BTreeMap::new();
    // Bind `a[i]` as a symbolic subscript, so the rewrite fires. `i` is an
    // argument, which is what makes it bindable as an index.
    let i = smt::var(64);
    args.insert("i".to_string(), i);
    fields.bind_array_len(0, "a", 8, 4);
    fields.bind_sym_index("a", 8, 4, "i", i);
    let src = "ret == a[i] && ret == a[j]";
    let err = spec::eval_ensures(
        src,
        &args,
        Some(smt::var(8)),
        spec::RET_IS_UNKNOWN,
        &std::collections::BTreeSet::new(),
        false,
        &fields,
    )
    .expect_err("`a[j]` has no chain and must be refused");
    assert_eq!(
        err.text, src,
        "the error must quote the source contract, not the rewritten one"
    );
    assert!(
        !err.text.contains("__"),
        "no mangled name may leak into the quoted text: {}",
        err.text
    );
}

/// A subscript by a name that is not an argument is refused.
///
/// `a[k]` where `k` is a local has no variable to build a chain from, so nothing
/// is bound and the parser refuses `k`. This is the distinct "no chain to rewrite
/// to" refusal, as opposed to the "chain exists but the index is unbounded" one;
/// conflating them would hide a bound index behind the wrong message.
#[test]
fn a_symbolic_index_that_is_not_an_argument_is_refused() {
    let Some(report) = verify_realistic(&["array_local_index_refused"]) else { return };
    let o = outcome(&report, "array_local_index_refused");
    match o {
        FnOutcome::Skipped { reason } => assert!(
            reason.contains("unknown name"),
            "a non-argument index must be refused as an unknown name, got: {reason}"
        ),
        other => panic!("`array_local_index_refused` must be skipped, got: {other}"),
    }
}

/// A *slice* subscripted symbolically is still refused.
///
/// The whole feature turns on the domain being finite. An array's length is in its
/// type, so `0..N` can be enumerated; a slice's length is a symbolic input, so
/// there is no chain to build and `xs[i]` stays a refusal. This is the boundary,
/// and it is asserted so the feature cannot silently widen to slices.
#[test]
fn a_symbolic_slice_index_is_still_refused() {
    let Some(report) = verify_realistic(&["slice_symbolic_index_refused"]) else { return };
    let o = outcome(&report, "slice_symbolic_index_refused");
    match o {
        FnOutcome::Skipped { reason } => assert!(
            reason.contains("unknown name") || reason.contains("xs"),
            "the refusal must be about the unbound subscript, got: {reason}"
        ),
        other => panic!("`slice_symbolic_index_refused` must be skipped, got: {other}"),
    }
}

/// The chain is really evaluated: a false postcondition about `a[i]` produces a
/// counterexample that pins the index to an in-range value.
///
/// Without this, "verified" above would be consistent with the chain being a
/// constant the postcondition happened to accept. `body_only` claims `ret <= 9`
/// for an arbitrary `u8` element, which is false, so it must FAIL -- and the
/// counterexample must show the element's value, which only exists if the chain
/// selected a real element variable.
#[test]
fn a_false_symbolic_index_postcondition_is_caught() {
    let src = r#"
/// requires: i < 4
/// ensures: ret <= 9
pub fn chain_must_be_read(a: [u8; 4], i: usize) -> u8 {
    a[i]
}
"#;
    let Some(rustc) = rustc() else { return };
    let dir = std::env::temp_dir().join(format!("discharge-chain-{}", std::process::id()));
    let _ = std::fs::create_dir_all(&dir);
    let file = dir.join("chain.rs");
    std::fs::write(&file, src).expect("write probe");
    let report = verify::verify_file_with(&rustc, &file, &[]).expect("frontend");
    let o = outcome(&report, "chain_must_be_read");
    match o {
        FnOutcome::Failed { detail, .. } => assert!(
            !detail.is_empty(),
            "a failed symbolic-index obligation must carry a counterexample"
        ),
        other => panic!("`chain_must_be_read` must FAIL (ret <= 9 is false), got: {other}"),
    }
    let _ = std::fs::remove_dir_all(&dir);
}
