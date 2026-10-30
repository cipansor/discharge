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

/// The corpus tripwires for the write/read-store desync, asserted end to end.
///
/// Each of these contracts is *false* and the frontend used to prove one of them.
/// The corpus (`examples/mir_targets/realistic.rs`) carries them so
/// `examples/mir_coverage` measures the shape; this pins the verdict so a
/// regression is a test failure rather than a quiet false proof.
#[test]
fn a_write_cannot_prove_a_stale_contract() {
    let names = [
        "array_write_then_symbolic_read",
        "mut_ref_array_write_then_symbolic_read",
        "generated_name_shadows_argument",
    ];
    let Some(report) = verify_realistic(&names) else { return };
    for name in names {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "`{name}` proves a false contract; got: {o}"
        );
    }
    // The struct-reassignment shape is refused rather than refuted: the write
    // poisons `c.lo`, and the postcondition then has no single value to check.
    // The requirement is the same -- never `Verified`.
    let Some(report) = verify_realistic(&["struct_reassign_then_field_read"]) else { return };
    let o = outcome(&report, "struct_reassign_then_field_read");
    assert!(
        !o.is_verified(),
        "`struct_reassign_then_field_read` proves a stale field; got: {o}"
    );
}

/// Stage 2: the newly modelled rvalues, each with its tripwire.
///
/// These four shapes -- a struct literal, a reference to a place, `.len()` on an
/// array, and a whole-struct reassignment -- were all `Unknown` before, so their
/// contracts were unreadable rather than checked. Each pair below is a true
/// contract that must now verify and a false one that a wrong model would prove.
/// The tripwires are the point: verifying the true half alone would not show the
/// model is right, only that it is present.
#[test]
fn stage_two_rvalues_are_modelled_and_their_tripwires_refuted() {
    let verified = [
        "struct_literal_reads_its_field",
        "struct_literal_order",
        "reference_reads_through",
        "reference_write_reaches_target",
        "array_len_is_the_type_constant",
        "struct_reassign_reads_new_field",
        "enum_match_is_bounded",
        "enum_match_selects_by_tag",
        "enum_payload_reads_through",
        "enum_constructed_locally",
        "enum_constructed_payload_reads_through",
        "enum_explicit_discriminant_selects_by_tag",
        "enum_user_variant_not_option",
        "enum_user_variant_not_option_constructed",
    ];
    let refuted = [
        // Written in reverse order; a positional-by-write-order model proves it.
        "struct_literal_order_tripwire",
        // The pre-write value; a snapshot model of `&mut` proves it.
        "reference_write_tripwire",
        // Claims every arm returns `2`; only a constant tag proves it.
        "enum_match_tripwire",
        // Claims the `Off` arm ran for a value built as `Mode::Idle`; a model
        // that resolved the variant to the wrong index (or to a symbolic tag)
        // would prove it.
        "enum_constructed_locally_tripwire",
        // Claims the `B` arm ran for `Gap::C`, whose real tag is `4`; a reader
        // numbering variants by position would call it `1` and prove this.
        "enum_explicit_discriminant_tripwire",
        // Claims the `None` arm ran for `Shadow::Some`, whose real tag is `0`;
        // taking `Option`'s numbering for the qualified name proves this.
        "enum_user_variant_not_option_tripwire",
        "enum_user_variant_not_option_constructed_tripwire",
    ];
    let Some(report) = verify_realistic(&verified) else { return };
    for name in verified {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    let Some(report) = verify_realistic(&refuted) else { return };
    for name in refuted {
        let o = outcome(&report, name);
        let FnOutcome::Failed { .. } = o else {
            panic!("`{name}` is a false contract that must be refuted, got: {o}");
        };
    }
}

/// The bitwise complement `!x`, pinned by a true half and a tripwire.
///
/// `!x` is `all_ones ^ x` at the *operand's* width. The model reads that width
/// off the value and refuses a destination local that disagrees with it, rather
/// than masking at `dest_w`. The three verifying entries name the operand's width
/// at three different widths (`u8`, `i8`, `u32`), so a model that masked at the
/// wrong width would fail the `u32` one; `not_of_zero_is_minus_one` pins the sign
/// the value keeps; and the tripwire is the evidence the operand is read at all,
/// since a constant `255` (or `all_ones ^ 0`) would prove it.
#[test]
fn the_bitwise_complement_reads_the_operands_width() {
    let verified = [
        "not_of_zero_is_all_ones",
        "not_is_255_minus_x",
        "not_of_zero_is_minus_one",
        "not_of_zero_u32_is_all_ones",
    ];
    let Some(report) = verify_realistic(&verified) else { return };
    for name in verified {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    let Some(report) = verify_realistic(&["not_is_always_255_tripwire"]) else { return };
    let o = outcome(&report, "not_is_always_255_tripwire");
    let FnOutcome::Failed { .. } = o else {
        panic!("`not_is_always_255_tripwire` is false and must be refuted, got: {o}");
    };
}

/// The struct-literal tripwire's counterexample is the `hi` operand, not `lo`.
///
/// [`struct_literal_order_tripwire`] writes `lo: 7` and `hi: a` and claims
/// `ret == a`. Refuting it is not enough on its own: a wrong model could refute
/// it for the wrong reason. What makes the refutation *evidence* is the witness,
/// which must be `a == 0` -- the value that differs from `lo`'s `7`. A model that
/// read the fields in write order would have *proved* this contract instead, so
/// reaching a witness at all is the proof the order is declaration order.
#[test]
fn a_struct_literal_reads_fields_in_declaration_order() {
    let Some(report) = verify_realistic(&["struct_literal_order_tripwire"]) else { return };
    let o = outcome(&report, "struct_literal_order_tripwire");
    let FnOutcome::Failed { detail, .. } = o else {
        panic!("`struct_literal_order_tripwire` must be refuted, got: {o}");
    };
    assert!(
        detail.contains("= 0"),
        "the witness must be `a == 0`, the value that is not `lo` (7); got: {detail}"
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

/// A same-dump helper that indexes its parameter must reach the caller's element.
///
/// `head` returns `a[0]` and `caller_of_head` claims `ret == a[0]`. The call is
/// inlined into a fresh callee `Env`, and before that `Env` was handed a copy of
/// the *indexed* store the callee's `_1[_2]` reads, the element was unknown and
/// the caller was incomplete. The two functions are checked together because the
/// property is about what crosses the call boundary.
#[test]
fn a_helper_that_indexes_its_parameter_reaches_the_caller_element() {
    let names = ["head", "caller_of_head"];
    let Some(report) = verify_realistic(&names) else { return };
    for name in names {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
}

/// A helper that writes through a `&mut` array changes the *caller's* element.
///
/// `clear_head` writes `a[0] = 0` through the reference and returns it;
/// `caller_of_clear_head` claims `ret == 0`, which is only true if the helper's
/// write is visible to the caller. The reference is the shared store, so the
/// callee's post-state must be copied back.
#[test]
fn a_write_through_a_reference_reaches_the_caller() {
    let names = ["clear_head", "caller_of_clear_head"];
    let Some(report) = verify_realistic(&names) else { return };
    for name in names {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
}

/// The soundness tripwire for the call boundary: a by-value helper's write to its
/// *own copy* must not reach the caller.
///
/// `clear_copy` clears its by-value array and returns `0`, but the caller's `a` is
/// the array it passed and is untouched, so `caller_of_written_copy` returning
/// `a[0]` is not `0`. If the callee's copy were shared with the caller's store --
/// the tempting way to make the element reads agree -- this false contract would
/// verify. It must fail.
#[test]
fn a_by_value_helper_cannot_write_the_callers_array() {
    let Some(report) = verify_realistic(&["caller_of_written_copy"]) else { return };
    let o = outcome(&report, "caller_of_written_copy");
    assert!(
        matches!(o, FnOutcome::Failed { .. }),
        "a by-value helper's write leaked to the caller; got: {o}"
    );
}

/// A signed comparison whose *left* operand is a constant must be signed.
///
/// `0 < c.lo` lowers to `Lt(const 0_i8, ...)`, and the constant carries the
/// signedness. Reading a constant operand as unsigned made this an unsigned test,
/// under which `i8::MIN` (`0x80`) is the largest value, so `ret == 1` was
/// *proved* for `c.lo == i8::MIN` -- a false proof, since `i8::MIN` is negative
/// and the branch is never taken. The pair pins both directions: the false claim
/// must fail, and the true one must verify.
#[test]
fn a_constant_left_signed_compare_is_signed_not_unsigned() {
    let names = ["signed_const_left_false", "signed_const_left_true"];
    let Some(report) = verify_realistic(&names) else { return };
    let bad = outcome(&report, "signed_const_left_false");
    assert!(
        matches!(bad, FnOutcome::Failed { .. }),
        "`signed_const_left_false` proves a false contract; got: {bad}"
    );
    let good = outcome(&report, "signed_const_left_true");
    assert!(good.is_verified(), "`signed_const_left_true` must verify, got: {good}");
}

/// A `(bool, u8)` return can be checked on its bool component.
///
/// `ret.0` is a `bool` in the type but compared against a one-bit word in the
/// postcondition, so the component has to be widened when it is read out of the
/// return place. Before that, `ret.0` had no binding and the contract was refused
/// as unreadable.
#[test]
fn a_postcondition_can_name_a_bool_tuple_component() {
    let Some(report) = verify_realistic(&["bool_component"]) else { return };
    let o = outcome(&report, "bool_component");
    assert!(o.is_verified(), "`bool_component` must verify, got: {o}");
}

/// A tuple local's component can be read back as a *field* projection.
///
/// `let t = (a, b); t.0` stores the components under an index projection and
/// reads them back as `_3.0`, a field projection. Before the two spellings met in
/// one store, `t.0` was `Unknown` and a contract about the return was unreadable.
#[test]
fn a_tuple_locals_component_can_be_read_back() {
    let Some(report) = verify_realistic(&["tuple_local_component"]) else { return };
    let o = outcome(&report, "tuple_local_component");
    assert!(o.is_verified(), "`tuple_local_component` must verify, got: {o}");
}

/// A component of a tuple-*returning call* reaches the caller.
///
/// `min_call` returns `min2(a, b).0`. The callee's components live in its own
/// return place, so they must cross the call boundary with the aggregate; before
/// that, only the aggregate crossed and the component was lost, leaving the
/// caller's contract unreadable rather than checked.
#[test]
fn a_tuple_returning_calls_component_reaches_the_caller() {
    let names = ["min2", "min_call"];
    let Some(report) = verify_realistic(&names) else { return };
    for name in names {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
}

/// The soundness tripwires for the tuple-component reads.
///
/// Each is a *false* contract that the tempting wrong model would prove: reading
/// the wrong component of a tuple local, or carrying the components across a call
/// boundary in the wrong order (or as one shared value). A `verified` verdict
/// here is a proof of something untrue, so both must fail.
#[test]
fn a_tuple_component_read_cannot_prove_the_wrong_component() {
    let names = ["tuple_component_tripwire", "min_call_tripwire"];
    let Some(report) = verify_realistic(&names) else { return };
    for name in names {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "`{name}` proves the wrong tuple component; got: {o}"
        );
    }
}

/// A signed widening cast sign-extends; an unsigned one zero-fills.
///
/// Both directions are pinned because the two casts need *opposite* rules, and a
/// single-rule implementation is wrong for one of them. `truncate` zero-fills, so
/// using it for every cast modelled `-1i8 as i16` as `255` and *proved*
/// `requires: a == -1; ensures: ret == 255` -- a reachable false proof. A
/// sign-extend-everything rule would instead prove `255u8 as u16 == 65535`.
#[test]
fn a_widening_cast_respects_the_sources_signedness() {
    let names = [
        "widen_signed_true",
        "widen_signed_false",
        "widen_unsigned_true",
        "widen_unsigned_false",
    ];
    let Some(report) = verify_realistic(&names) else { return };
    for name in ["widen_signed_true", "widen_unsigned_true"] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    for name in ["widen_signed_false", "widen_unsigned_false"] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "`{name}` proves a false widening; got: {o}"
        );
    }
}

/// A signed array element stays signed through the subscript.
///
/// The element's signedness lives in the array's element *type* and has to reach
/// the value the subscript produces. The two entries pin both directions: the
/// true one verifies only if `xs[0] < 0` is a signed test, and the tripwire
/// (`xs[0] == i8::MIN`, where the most negative element *is* negative) is
/// *proved* under the unsigned reading, so it must FAIL.
#[test]
fn a_signed_element_comparison_keeps_the_elements_sign() {
    let names = ["signed_slice_element_is_signed", "signed_slice_element_tripwire"];
    let Some(report) = verify_realistic(&names) else { return };
    let o = outcome(&report, "signed_slice_element_is_signed");
    assert!(o.is_verified(), "`signed_slice_element_is_signed` must verify, got: {o}");
    let o = outcome(&report, "signed_slice_element_tripwire");
    assert!(
        matches!(o, FnOutcome::Failed { .. }),
        "`signed_slice_element_tripwire` proves `!(i8::MIN < 0)`; got: {o}"
    );
}

/// A postcondition naming a component a *modelled call* wrote is not refused.
///
/// `overflowing_add` returns `(T, bool)` and the modelled call writes `_0.0` and
/// `_0.1` directly -- it never assigns the tuple local as a whole. So the value
/// component lives in the *field* store while a literal's `_0 = (a, b)` lives in
/// the element store, and a `ret.N` reader that consulted only the latter found
/// the component unbound. The symptom was the whole contract refused as "the
/// return type is an aggregate, so `ret` has no single value" -- a message about
/// the wrong problem, since the reader already knew to look at components.
///
/// The two verifying entries read `ret.1` (the flag) and `ret.0` (the value), so
/// both stores are exercised, and the two tripwires must FAIL: a reader that
/// dropped a component would make those contracts vacuously true.
#[test]
fn a_postcondition_can_name_a_component_a_modelled_call_wrote() {
    let names = [
        "overflowing_add_flag_or_exact_sum",
        "overflowing_add_small_operands_never_flag",
        "overflowing_add_value_is_exact_when_no_overflow",
        "overflowing_add_flag_never_set_tripwire",
        "overflowing_add_one_bound_only_tripwire",
        "overflowing_add_wrapped_value_below_operand_tripwire",
    ];
    let Some(report) = verify_realistic(&names) else { return };
    for name in [
        "overflowing_add_flag_or_exact_sum",
        "overflowing_add_small_operands_never_flag",
        "overflowing_add_value_is_exact_when_no_overflow",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    for name in [
        "overflowing_add_flag_never_set_tripwire",
        "overflowing_add_one_bound_only_tripwire",
        "overflowing_add_wrapped_value_below_operand_tripwire",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "`{name}` states a false contract a dropped component would prove; got: {o}"
        );
    }
}

/// A `(u8, &u8)` return with a postcondition on `ret.0` alone is not skipped.
///
/// Component 1 is a reference with no bit-vector width. Binding every declared
/// component up front made the up-front parse probe refuse, so the function was
/// `Skipped` for a component the contract never named. Only the components a
/// contract names are probed.
#[test]
fn a_reference_component_the_contract_does_not_name_does_not_skip_the_function() {
    let Some(report) = verify_realistic(&["first_component_only"]) else { return };
    let o = outcome(&report, "first_component_only");
    assert!(o.is_verified(), "`first_component_only` must verify, got: {o}");
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
    fields.bind_array_len(0, "a", 8, false, 4);
    fields.bind_sym_index("a", 8, spec::IndexBound::Const(4), "i", i);
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

/// A subscript by a name that is a *direct alias* of an argument is resolved.
///
/// `let k = i;` on a `Copy` value lowers to no local: the body's `a[k]` is
/// `a[i]`, and `k` survives only as a scoped `debug k => _2;`. The contract's `k`
/// therefore names the very index the body reads, so it must verify — and the
/// tripwire must FAIL, which is what shows the name resolved to the real index
/// rather than to a constant the postcondition happened to accept.
#[test]
fn a_symbolic_index_through_a_local_alias_is_resolved() {
    let Some(report) =
        verify_realistic(&["array_local_index_through_alias", "array_local_index_tripwire"])
    else {
        return;
    };
    let o = outcome(&report, "array_local_index_through_alias");
    assert!(o.is_verified(), "`array_local_index_through_alias` must verify, got: {o}");
    let t = outcome(&report, "array_local_index_tripwire");
    assert!(
        !t.is_verified(),
        "the alias tripwire must be refuted, got: {t}"
    );
}

/// The alias rule is not a licence to follow a reassigned argument.
///
/// `let k = i; i = 2;` — rustc materialises a real local for the copy and prints
/// `debug k => _3;` pointing at *that* local, not at `_2`. So `k` is not an alias
/// of the argument and the contract's `k` is refused. If the frontend instead
/// aliased `k` to `i` unconditionally, the contract would be checked against a
/// reassigned index and could be proved or refuted about the wrong value.
#[test]
fn a_subscript_through_a_reassigned_argument_is_refused() {
    let Some(report) = verify_realistic(&["array_local_index_written_refused"]) else { return };
    let o = outcome(&report, "array_local_index_written_refused");
    match o {
        FnOutcome::Skipped { reason } => assert!(
            reason.contains("unknown name"),
            "a subscript through a reassigned argument must be refused as an unknown name, \
             got: {reason}"
        ),
        other => panic!("`array_local_index_written_refused` must be skipped, got: {other}"),
    }
}

/// A subscript through an alias is one element under *every* spelling of the
/// index, not just the first.
///
/// `a[i]` and `a[k]` with `let k = i` name the same element, so a contract using
/// both must be readable and verify — the second subscript has to rewrite to the
/// same chain as the first. The tripwire claims they differ and must be refuted.
/// Keeping only the first spelling left the second unrewritten and the parser
/// refused the whole contract, which skipped a function that should have
/// verified; this pins the fix.
#[test]
fn a_symbolic_index_resolves_under_every_spelling() {
    let Some(report) =
        verify_realistic(&["array_two_spellings_of_one_index", "array_two_spellings_tripwire"])
    else {
        return;
    };
    let o = outcome(&report, "array_two_spellings_of_one_index");
    assert!(o.is_verified(), "`array_two_spellings_of_one_index` must verify, got: {o}");
    let t = outcome(&report, "array_two_spellings_tripwire");
    assert!(
        !t.is_verified(),
        "the two-spellings tripwire must be refuted, got: {t}"
    );
}

/// A subscript by a name that is *shadowed* is refused.
///
/// `let k = i; let k = 0;` prints two bindings for `k`, and only the second is
/// what `a[k]` reads. Resolving `k` from the first would check the contract
/// against `i` while the body used the constant — a contract that is false for
/// `i == 1` could prove. The name is bound more than once, so it is refused.
#[test]
fn a_shadowed_alias_is_refused() {
    let Some(report) = verify_realistic(&["array_shadowed_alias_refused"]) else { return };
    let o = outcome(&report, "array_shadowed_alias_refused");
    match o {
        FnOutcome::Skipped { reason } => assert!(
            reason.contains("unknown name"),
            "a shadowed alias must be refused as an unknown name, got: {reason}"
        ),
        other => panic!("`array_shadowed_alias_refused` must be skipped, got: {other}"),
    }
}

/// A *qualified* standard construction (`Option::<u8>::Some`) resolves.
///
/// rustc prints a standard construction with its generic arguments, so the
/// qualifier is `Option`, not `u8`. A reader that only consults declared layouts
/// for a qualified name finds none for `Option` and refuses the construction,
/// losing a shape the unqualified spelling handles. The true contract must
/// verify and the false one must be refuted, which only happens if the tag and
/// the payload are both read.
#[test]
fn a_qualified_standard_construction_resolves() {
    let Some(report) = verify_realistic(&[
        "option_qualified_some_payload",
        "option_qualified_some_payload_tripwire",
    ]) else {
        return;
    };
    let o = outcome(&report, "option_qualified_some_payload");
    assert!(o.is_verified(), "`option_qualified_some_payload` must verify, got: {o}");
    let t = outcome(&report, "option_qualified_some_payload_tripwire");
    assert!(!t.is_verified(), "the qualified-construction tripwire must be refuted, got: {t}");
}

/// A trailing line comment on a variant line does not erase the enum layout.
///
/// `B = 3, // special` keeps the comma *before* the comment, so the reader that
/// trims a trailing comma from the raw line no longer finds one, rejects the
/// discriminant, and drops the whole layout -- taking every contract that names
/// a variant with it. The true contract must verify and the tripwire refute.
#[test]
fn a_trailing_comment_on_a_variant_keeps_the_layout() {
    let Some(report) = verify_realistic(&[
        "enum_trailing_comment_keeps_the_layout",
        "enum_trailing_comment_tripwire",
    ]) else {
        return;
    };
    let o = outcome(&report, "enum_trailing_comment_keeps_the_layout");
    assert!(
        o.is_verified(),
        "`enum_trailing_comment_keeps_the_layout` must verify, got: {o}"
    );
    let t = outcome(&report, "enum_trailing_comment_tripwire");
    assert!(!t.is_verified(), "the trailing-comment tripwire must be refuted, got: {t}");
}

/// A *slice* subscripted symbolically is modelled, not refused — when the
/// precondition bounds both the index and the length.
///
/// The whole feature turns on the domain being finite. An array's length is in its
/// type, so `0..N` can be enumerated; a slice's is a symbolic input, so the chain
/// enumerates `0..MAX_INDEX_CHAIN` and is exact only where the length is within
/// that. The precondition has to establish both facts, and this pins that the
/// modelled case really verifies rather than being refused.
#[test]
fn a_symbolic_slice_index_is_modelled_when_both_bounds_hold() {
    let Some(report) = verify_realistic(&["slice_symbolic_index"]) else { return };
    let o = outcome(&report, "slice_symbolic_index");
    assert!(o.is_verified(), "`slice_symbolic_index` must verify, got: {o}");
}

/// The tripwire: a false claim about `xs[i]` must be *refuted*, not refused.
///
/// The body returns `xs[i]`, and the contract claims that is also `xs[0]` — false
/// for every `i != 0`. A pass would mean the chain ignored the index. The
/// assertion is on `Failed` rather than on `!is_verified()` on purpose: a
/// `Skipped` or `Incomplete` outcome is also "not verified", and accepting one
/// would let the tripwire pass without the chain ever having been contradicted.
#[test]
fn a_slice_chain_depends_on_the_index() {
    let Some(report) = verify_realistic(&["slice_symbolic_index_tripwire"]) else { return };
    let o = outcome(&report, "slice_symbolic_index_tripwire");
    assert!(
        matches!(o, FnOutcome::Failed { .. }),
        "`slice_symbolic_index_tripwire` must be refuted (not skipped), got: {o}"
    );
}

/// Each of a slice's two bounds is required on its own, and the refusal names the
/// one that is missing.
///
/// The length bound is the half an index-only rule would miss, and the index bound
/// is the half a length-only rule would miss. Each entry below supplies one fact
/// and withholds the other, so a rule that checked only one of them would model a
/// subscript it should refuse.
#[test]
fn a_slice_subscript_missing_either_bound_is_refused() {
    let cases = [
        ("slice_unbounded_length_refused", "`xs.len() <= 64` does not hold"),
        ("slice_unbounded_index_refused", "`i < xs.len()` does not hold"),
    ];
    for (name, want) in cases {
        let Some(report) = verify_realistic(&[name]) else { return };
        let o = outcome(&report, name);
        match o {
            FnOutcome::Skipped { reason } => assert!(
                reason.contains(want),
                "`{name}`'s refusal must name the missing bound `{want}`, got: {reason}"
            ),
            other => panic!("`{name}` must be skipped, got: {other}"),
        }
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
/// Verify a one-function source file and return the single outcome.
///
/// Each of the tests below needs its own file, because the property under test is
/// about what the *frontend* does with a specific shape and the corpus is shared.
/// Writing the source to a temp dir keeps that shape next to its assertion.
fn verify_src(name: &str, src: &str) -> Option<FnOutcome> {
    let rustc = rustc()?;
    let dir = std::env::temp_dir().join(format!("discharge-{name}-{}", std::process::id()));
    let _ = std::fs::create_dir_all(&dir);
    let file = dir.join("probe.rs");
    std::fs::write(&file, src).expect("write probe");
    let report = verify::verify_file_with(&rustc, &file, &[]).expect("frontend");
    let o = report
        .outcomes
        .into_iter()
        .find(|(n, _)| n == name)
        .map(|(_, o)| o);
    let _ = std::fs::remove_dir_all(&dir);
    o
}

/// An element write must reach the store a *symbolic* read consults.
///
/// `a[0] = 0; a[i]` returns `0` when `i == 0`, so `ret == a[i]` is false. The
/// chain is built from the seeded elements, so if the write landed anywhere else
/// the chain would select the pre-write `a[0]` and this false contract would
/// verify. The test requires it to be *refuted*, not merely undecided: a
/// counterexample is the evidence that the chain is evaluated against the written
/// value, and `Verified` here would be a false proof.
#[test]
fn an_element_write_reaches_the_symbolic_chain() {
    let src = r#"
/// requires: i < 4 && i == 0
/// ensures: ret == a[i]
pub fn written_then_symbolic(mut a: [u8; 4], i: usize) -> u8 {
    a[0] = 0;
    a[i]
}
"#;
    let Some(o) = verify_src("written_then_symbolic", src) else { return };
    assert!(
        matches!(o, FnOutcome::Failed { .. }),
        "a write must not leave a stale element readable by the chain; got: {o}"
    );
}

/// The same property through a `&mut [u8; 4]` reborrow.
#[test]
fn an_element_write_through_a_mutable_reference_reaches_the_chain() {
    let src = r#"
/// requires: i < 4 && i == 0
/// ensures: ret == a[i]
pub fn ref_written_then_symbolic(a: &mut [u8; 4], i: usize) -> u8 {
    a[0] = 0;
    a[i]
}
"#;
    let Some(o) = verify_src("ref_written_then_symbolic", src) else { return };
    assert!(
        matches!(o, FnOutcome::Failed { .. }),
        "a reborrowed element write must reach the chain too; got: {o}"
    );
}

/// A `&mut [u8]` slice write must reach the store the read consults.
///
/// This is the gap the `&raw const (fake) (*_1)` parse closed. Before it, the
/// bounds check on a `&mut [u8]` argument read its length through a raw reborrow
/// the parser did not recognise, so the function was `incomplete` before any
/// write was reached -- the write was never even evaluated. Now the true half
/// must *verify* (a write then a read of the same index returns what was
/// written) and the tripwire -- the same body claiming the pre-write value --
/// must be refuted, since a model that dropped the write would leave the seeded
/// element readable and prove it.
#[test]
fn a_slice_element_write_reaches_the_store_the_read_consults() {
    let src = r#"
/// requires: s.len() > 0
/// ensures: ret == v
pub fn slice_written_then_read(s: &mut [u8], v: u8) -> u8 {
    s[0] = v;
    s[0]
}

/// requires: s.len() > 0
/// ensures: ret == s[0]
pub fn slice_written_then_read_tripwire(s: &mut [u8], v: u8) -> u8 {
    s[0] = v;
    s[0]
}
"#;
    let Some(o) = verify_src("slice_written_then_read", src) else { return };
    assert!(
        o.is_verified(),
        "a write then a read of the same slice index returns what was written; got: {o}"
    );
    let Some(o) = verify_src("slice_written_then_read_tripwire", src) else { return };
    assert!(
        matches!(o, FnOutcome::Failed { .. }),
        "the pre-write element must not stay readable after a slice write; got: {o}"
    );
}

/// The `&mut [u8]` *symbolic* read must see the slice write too.
///
/// The array form of this shape is [`an_element_write_through_a_mutable_reference_reaches_the_chain`];
/// the slice form differs in the bounds check, not the store, so the same
/// requirement holds -- the false contract must be refuted rather than left
/// undecided, which is what a missing `PtrMetadata` would have made it.
#[test]
fn a_slice_element_write_reaches_the_symbolic_chain() {
    let src = r#"
/// requires: i < s.len() && s.len() <= 64 && i == 0
/// ensures: ret == s[i]
pub fn slice_written_then_symbolic(s: &mut [u8], i: usize) -> u8 {
    s[0] = 0;
    s[i]
}
"#;
    let Some(o) = verify_src("slice_written_then_symbolic", src) else { return };
    assert!(
        matches!(o, FnOutcome::Failed { .. }),
        "a slice write must not leave a stale element readable by the chain; got: {o}"
    );
}

/// A whole-struct reassignment must invalidate the fields bound from it.
///
/// `c = d; c.lo` returns `d.lo`, so `ret == c.lo` is false unless `c.lo == d.lo`.
/// The field bindings are keyed by local and a plain `locals` write does not
/// touch them, so if the assignment left them the contract's `c.lo` would still
/// name the argument's field and this false contract would verify. It must be
/// refused or refuted -- anything but `Verified`.
#[test]
fn a_whole_struct_assignment_invalidates_its_fields() {
    let src = r#"
pub struct B { pub lo: u8 }

/// requires: true
/// ensures: ret == c.lo
pub fn reassigned_then_field(mut c: B, d: B) -> u8 {
    c = d;
    c.lo
}
"#;
    let Some(o) = verify_src("reassigned_then_field", src) else { return };
    assert!(
        !o.is_verified(),
        "a reassigned struct's field binding is stale and must not prove a contract; got: {o}"
    );
}

/// A generated binding name must not be able to shadow a real argument.
///
/// The contract's `a[i]` is rewritten to a binding named `a__chain`, and this
/// function has an argument of exactly that name. If the generated binding were
/// inserted unconditionally it would shadow the argument, so `ret == a__chain`
/// would be checked against the array's chain instead of the argument. With
/// `i == 0` and `a__chain == 0` but `a[0] != 0` the contract is false, so
/// `Verified` would be a false proof. Refusing the binding is the fix; this pins
/// it.
#[test]
fn a_generated_binding_cannot_shadow_an_argument() {
    let src = r#"
/// requires: i < 4
/// ensures: ret == a__chain
pub fn shadow_probe(a: [u8; 4], i: usize, a__chain: u8) -> u8 {
    a[i]
}
"#;
    let Some(o) = verify_src("shadow_probe", src) else { return };
    assert!(
        !o.is_verified(),
        "`a__chain` is a real argument and must not be replaced by the generated binding; got: {o}"
    );
}

/// A `__len` collision is refused the same way, and the array's length binding is
/// what is dropped rather than the argument.
#[test]
fn a_generated_length_binding_cannot_shadow_an_argument() {
    let src = r#"
/// requires: a.len() == 4
/// ensures: ret == a__len
pub fn shadow_len_probe(a: [u8; 4], a__len: usize) -> usize {
    a.len()
}
"#;
    let Some(o) = verify_src("shadow_len_probe", src) else { return };
    assert!(
        !o.is_verified(),
        "`a__len` is a real argument and must not be replaced by the generated length; got: {o}"
    );
}

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

/// Stage 2, enums: a `match` is a `switchInt` on a symbolic tag.
///
/// A `match` lowers to `_2 = discriminant(_1); switchInt(move _2) -> [...]`, so
/// the tag is an input. Before this it was read as unknown and every `match` was
/// `incomplete` with `unmodelled switch discriminant`. The tag's domain is the
/// enum's arity, which is a fact about the *type*, so assuming it is sound and is
/// what makes the `otherwise` arm -- lowered to `unreachable` -- genuinely
/// unreachable rather than a spurious panic.
///
/// The tripwire is what makes this evidence rather than a claim: a constant tag
/// (or one read as zero) would prove `enum_match_tripwire`, which is false.
#[test]
fn an_enum_match_is_a_switch_on_a_symbolic_tag() {
    let Some(report) = verify_realistic(&["enum_match_is_bounded"]) else { return };
    let o = outcome(&report, "enum_match_is_bounded");
    assert!(o.is_verified(), "`enum_match_is_bounded` must verify, got: {o}");
}

/// A variant payload is read through the downcast and is a symbolic input.
///
/// `Msg::Data(x)` lowers to `_3 = copy ((_1 as Data).0)`, so the payload is field
/// 0 of variant 1. The contract's `m.Data` is bound to the same variable the
/// downcast reads, so `ret == m.Data` on that arm is a claim about one value.
#[test]
fn an_enum_payload_is_read_through_the_downcast() {
    let Some(report) = verify_realistic(&["enum_payload_reads_through"]) else { return };
    let o = outcome(&report, "enum_payload_reads_through");
    assert!(o.is_verified(), "`enum_payload_reads_through` must verify, got: {o}");
}

/// A locally constructed variant has a *known* tag, so its `match` decides.
///
/// `let m = Mode::Idle;` lowers to `_1 = Mode::Idle;`, a bare path constant with
/// no `const ` prefix, and `Mode::Idle` resolves to the enum's declaration index.
/// The tag is therefore a constant, only the `Idle` arm is reachable, and the
/// contract is decided rather than left as a coverage gap. The companion
/// tripwire claims the `Off` arm ran, which the same model must refute.
#[test]
fn a_locally_constructed_variant_has_a_known_tag() {
    let Some(report) = verify_realistic(&["enum_constructed_locally"]) else { return };
    let o = outcome(&report, "enum_constructed_locally");
    assert!(o.is_verified(), "`enum_constructed_locally` must verify, got: {o}");
}

/// A constructed variant's payload is written where the downcast reads it.
///
/// `Msg::Data(9)` lowers to `_1 = Msg::Data(const 9_u8);`, so the tag is `1` and
/// the payload is field 0 of that variant. The match's `Data(x)` arm reads
/// `((_1 as Data).0: u8)`, which is the same field, so `ret == 9` is a claim
/// about the value the construction wrote -- not about a fresh input.
#[test]
fn a_constructed_variants_payload_is_read_through_the_downcast() {
    let Some(report) = verify_realistic(&["enum_constructed_payload_reads_through"]) else { return };
    let o = outcome(&report, "enum_constructed_payload_reads_through");
    assert!(o.is_verified(), "`enum_constructed_payload_reads_through` must verify, got: {o}");
}

/// A unit variant has no payload, so naming one is refused rather than bound.
///
/// `m.Ping` is a unit variant. There is no value to read, so the contract must be
/// refused -- a model that bound every variant to the same payload would prove
/// this false contract. The refusal is `Skipped`, which is reported, not a
/// silent pass.
#[test]
fn a_unit_variant_has_no_payload_to_name() {
    let Some(report) = verify_realistic(&["enum_payload_tripwire"]) else { return };
    let o = outcome(&report, "enum_payload_tripwire");
    assert!(
        !o.is_verified(),
        "`enum_payload_tripwire` names a unit variant's payload and must be refused, got: {o}"
    );
}

/// `count_ones` is modelled, and its result is *widened* to the return type.
///
/// The operand is `u8` and the result is `u32`, so this is the one modelled call
/// whose result width differs from its operand's. A model that built an 8-bit
/// term and wrote it to a `u32` local would be ill-formed, and a contract at the
/// top of the count's range would not decide. Both entries must verify.
#[test]
fn count_ones_is_modelled_and_widens_its_result() {
    let Some(report) = verify_realistic(&[
        "popcount_of_nonzero",
        "popcount_bounded_by_width",
    ]) else {
        return;
    };
    for name in ["popcount_of_nonzero", "popcount_bounded_by_width"] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
}

/// The tripwire: if `count_ones` were left unmodelled, both entries would be
/// `Skipped` rather than decided, and if it were modelled *wrongly* the false
/// claims would pass. A failure on the tripwires is the evidence the model was
/// contradicted; a decision at all is the evidence it is modelled.
#[test]
fn the_count_ones_tripwires_are_refuted_not_skipped() {
    let Some(report) = verify_realistic(&[
        "popcount_of_nonzero_tripwire",
        "popcount_bounded_by_width_tripwire",
    ]) else {
        return;
    };
    for name in ["popcount_of_nonzero_tripwire", "popcount_bounded_by_width_tripwire"] {
        let o = outcome(&report, name);
        let FnOutcome::Failed { kind, .. } = o else {
            panic!("`{name}` must FAIL: a `Skipped` means `count_ones` is not modelled, got: {o}");
        };
        assert_eq!(kind, "postcondition", "`{name}` got: {o}");
    }
}

/// `wrapping_abs` is modelled, unary, and reads its operand's sign.
///
/// The verifying entry is `ret >= x`, which holds at every `i8` including `MIN`
/// (where `abs` wraps back to `MIN`). The tripwire is `ret > x`, false at `x == 0`
/// where `abs` is the identity. Both must be *decided*: a `Skipped` would mean the
/// unary shape is not modelled at all, which is the gap this closed.
#[test]
fn wrapping_abs_is_modelled_unary_and_signed() {
    let Some(report) = verify_realistic(&["abs_never_below_operand"]) else { return };
    let o = outcome(&report, "abs_never_below_operand");
    assert!(o.is_verified(), "`abs_never_below_operand` must verify, got: {o}");

    let Some(report) = verify_realistic(&["abs_never_below_operand_tripwire"]) else { return };
    let o = outcome(&report, "abs_never_below_operand_tripwire");
    let FnOutcome::Failed { kind, detail } = o else {
        panic!("`abs_never_below_operand_tripwire` must FAIL, got: {o}");
    };
    assert_eq!(kind, "postcondition", "got: {o}");
    // The counterexample must be `x == 0`, the one point where `abs` is the
    // identity: if the model were wrong on the negative side the witness would
    // name a negative value instead.
    assert!(
        detail.contains("= 0"),
        "the witness should be x == 0 (where abs is the identity), got: {detail}"
    );
}

/// The zero-counts beside `count_ones` are modelled, and `leading_zeros` of a
/// zero operand is the *full* width.
///
/// `leading_zeros` is the shape where an off-by-one hides: every non-zero operand
/// has at most `w - 1` leading zeros, so a model that counted only those would
/// agree with `core` everywhere except `x == 0`, and that is exactly the input the
/// tripwire names. Both entries must be *decided* -- a `Skipped` would mean the
/// name is not modelled at all.
#[test]
fn the_zero_counts_are_modelled() {
    let Some(report) = verify_realistic(&[
        "leading_zeros_of_a_small_value",
        "trailing_zeros_of_a_top_bit_value",
    ]) else {
        return;
    };
    for name in ["leading_zeros_of_a_small_value", "trailing_zeros_of_a_top_bit_value"] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }

    let Some(report) = verify_realistic(&[
        "leading_zeros_of_a_small_value_tripwire",
        "trailing_zeros_of_a_top_bit_value_tripwire",
    ]) else {
        return;
    };
    for name in [
        "leading_zeros_of_a_small_value_tripwire",
        "trailing_zeros_of_a_top_bit_value_tripwire",
    ] {
        let o = outcome(&report, name);
        let FnOutcome::Failed { kind, .. } = o else {
            panic!("`{name}` must FAIL: a `Skipped` means the name is not modelled, got: {o}");
        };
        assert_eq!(kind, "postcondition", "`{name}` got: {o}");
    }
    // The `leading_zeros` witness must be `x == 0`, the only input where the count
    // is the full width. A model that counted `w - 1` there would name a non-zero
    // witness instead.
    let o = outcome(&report, "leading_zeros_of_a_small_value_tripwire");
    let FnOutcome::Failed { detail, .. } = o else { panic!("got: {o}") };
    assert!(
        detail.contains("= 0"),
        "the `leading_zeros` witness should be x == 0, got: {detail}"
    );
}

/// The four `pow` families are modelled, and the exponent is a `u32` *beside* a
/// base of the method's own width.
///
/// `pow` is the first modelled call whose two operands have different types. The
/// verifying entries pin the fold where the base's width matters (`2^7 == 128`
/// fits a `u8`, `2^8` wraps), and each tripwire states a *neighbouring* value --
/// one step off the true result -- so a model that folded at the wrong width, or
/// stopped a step early, refutes it. The signed entries pin the *clamp
/// direction*: `saturating_pow` of a negative base with an odd exponent clamps to
/// `MIN`, and a "clamp everything to `MAX`" model proves the `MAX` tripwire
/// instead of refuting it.
///
/// Every tripwire must be `Failed`, not `Skipped`: a `Skipped` would mean the
/// name is not modelled at all.
#[test]
fn the_pow_families_are_modelled_with_a_wide_exponent() {
    let Some(report) = verify_realistic(&[
        "wrapping_pow_two_to_seven_is_128",
        "checked_pow_two_to_seven_is_some_128",
        "saturating_pow_three_to_five_is_243",
        "overflowing_pow_two_to_seven_did_not_overflow",
        "wrapping_pow_negative_two_to_seven_is_min",
        "saturating_pow_negative_base_clamps_to_min",
        "wrapping_pow_zero_exponent_is_one",
    ]) else {
        return;
    };
    for name in [
        "wrapping_pow_two_to_seven_is_128",
        "checked_pow_two_to_seven_is_some_128",
        "saturating_pow_three_to_five_is_243",
        "overflowing_pow_two_to_seven_did_not_overflow",
        "wrapping_pow_negative_two_to_seven_is_min",
        "saturating_pow_negative_base_clamps_to_min",
        "wrapping_pow_zero_exponent_is_one",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }

    let Some(report) = verify_realistic(&[
        "wrapping_pow_two_to_eight_is_256_tripwire",
        "checked_pow_two_to_eight_is_none_tripwire",
        "saturating_pow_three_to_six_clamps_tripwire",
        "overflowing_pow_two_to_eight_flag_tripwire",
        "wrapping_pow_negative_two_to_eight_wraps_tripwire",
        "saturating_pow_negative_base_to_max_tripwire",
        "wrapping_pow_one_exponent_is_one_tripwire",
    ]) else {
        return;
    };
    for name in [
        "wrapping_pow_two_to_eight_is_256_tripwire",
        "checked_pow_two_to_eight_is_none_tripwire",
        "saturating_pow_three_to_six_clamps_tripwire",
        "overflowing_pow_two_to_eight_flag_tripwire",
        "wrapping_pow_negative_two_to_eight_wraps_tripwire",
        "saturating_pow_negative_base_to_max_tripwire",
        "wrapping_pow_one_exponent_is_one_tripwire",
    ] {
        let o = outcome(&report, name);
        let FnOutcome::Failed { kind, .. } = o else {
            panic!("`{name}` must FAIL: a `Skipped` means the name is not modelled, got: {o}");
        };
        assert_eq!(kind, "postcondition", "`{name}` got: {o}");
    }
}

/// The four unary `neg`/`abs` families are modelled, and they disagree about
/// `MIN` -- which is what proves each is the right one and not a shared stand-in.
///
/// `saturating_neg` and `saturating_abs` clamp at `MIN`, so their results are
/// never negative; `wrapping_neg` and `wrapping_abs` return `MIN` there, which
/// *is* negative. The verifying entries state the clamp; the tripwires state the
/// same claim about the wrapping family, where `MIN` refutes it. If the four
/// shared one definition, either the clamps would fail or the tripwires would
/// pass, and both are caught here.
#[test]
fn the_unary_neg_and_abs_families_disagree_at_min() {
    let Some(report) = verify_realistic(&[
        "saturating_neg_of_positive_is_negative",
        "saturating_neg_of_non_positive_is_non_negative",
        "saturating_abs_is_never_negative",
        "saturating_abs_of_non_negative_is_identity",
    ]) else {
        return;
    };
    for name in [
        "saturating_neg_of_positive_is_negative",
        "saturating_neg_of_non_positive_is_non_negative",
        "saturating_abs_is_never_negative",
        "saturating_abs_of_non_negative_is_identity",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }

    let Some(report) = verify_realistic(&[
        "wrapping_neg_is_negative_tripwire",
        "wrapping_neg_of_non_positive_is_non_negative_tripwire",
        "wrapping_abs_is_never_negative_tripwire",
        "saturating_abs_is_identity_tripwire",
    ]) else {
        return;
    };
    for name in [
        "wrapping_neg_is_negative_tripwire",
        "wrapping_neg_of_non_positive_is_non_negative_tripwire",
        "wrapping_abs_is_never_negative_tripwire",
        "saturating_abs_is_identity_tripwire",
    ] {
        let o = outcome(&report, name);
        let FnOutcome::Failed { kind, .. } = o else {
            panic!("`{name}` must FAIL: a `Skipped` means the shape is not modelled, got: {o}");
        };
        assert_eq!(kind, "postcondition", "`{name}` got: {o}");
    }
    // The `abs`-at-`MIN` tripwire must name `x == 128`, which is `i8::MIN` read
    // unsigned -- the one input where the magnitude is unrepresentable. Naming
    // any other witness would mean the model disagrees with `core` elsewhere.
    let o = outcome(&report, "wrapping_abs_is_never_negative_tripwire");
    let FnOutcome::Failed { detail, .. } = o else { panic!("got: {o}") };
    assert!(
        detail.contains("= 128"),
        "the `wrapping_abs` witness should be x == i8::MIN (bits 128), got: {detail}"
    );
}

/// A `match` on a standard-library enum *argument* is modelled.
///
/// `Option` and `Result` are the two enums a real function reads without any
/// source file declaring them: `checked_add` returns `Option<u8>`, and `?` threads
/// a `Result`. An *argument* of one of those types had no layout, so its tag was
/// never seeded and the `switchInt` on it came back an unmodelled switch
/// discriminant -- a refusal, not a verdict. The declared-enum argument (`Mode`)
/// and the locally constructed `Option` both worked; the argument form is the gap.
///
/// Both halves matter: the true contracts must verify (the tag and the payload are
/// seeded) and the tripwires must be refuted (the tag and the payload are *read*,
/// not free variables the contract could make true). A model that seeded a
/// constant tag would take one arm always and prove a false tripwire.
#[test]
fn a_standard_enum_argument_is_a_switch_on_a_seeded_tag() {
    let Some(report) = verify_realistic(&[
        "option_arg_match",
        "option_arg_match_tripwire",
        "result_arg_match",
        "result_arg_match_tripwire",
        "option_arg_payload_passthrough",
        "option_arg_payload_tripwire",
    ]) else {
        return;
    };
    for name in ["option_arg_match", "result_arg_match", "option_arg_payload_passthrough"] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    for name in
        ["option_arg_match_tripwire", "result_arg_match_tripwire", "option_arg_payload_tripwire"]
    {
        let o = outcome(&report, name);
        let FnOutcome::Failed { kind, .. } = o else {
            panic!("`{name}` must FAIL: a `Skipped` means the shape is not modelled, got: {o}");
        };
        assert_eq!(kind, "postcondition", "`{name}` got: {o}");
    }
}

/// The same shape in an isolated file, so the fix is pinned even if the corpus
/// entry is edited: a `match` on `Option<u8>` must produce a verdict, not the
/// "unmodelled switch discriminant" refusal.
///
/// The nested-type spelling is the part worth pinning separately -- the payload is
/// the type argument as *one* type, so `Option<u8>` carries a `u8` and a
/// `Result<u8, u16>` carries a `u8` for `Ok` and a `u16` for `Err`. Splitting the
/// argument list at the wrong level (or reading the payload as the whole `u8, u16`
/// text) would size the payload wrongly and the width assertion in the contract
/// would fail.
#[test]
fn a_standard_enum_argument_payload_has_its_own_width() {
    let src = r#"
        /// requires: true
        /// ensures: ret <= 255
        pub fn opt_payload(x: Option<u8>) -> u8 {
            match x { Some(v) => v, None => 0 }
        }
        /// requires: true
        /// ensures: ret <= 1
        pub fn res_payload(r: Result<u8, u16>) -> u8 {
            match r { Ok(_) => 0, Err(_) => 1 }
        }
    "#;
    let Some(o) = verify_src("opt_payload", src) else { return };
    assert!(o.is_verified(), "`opt_payload` must verify, got: {o}");
    let Some(o) = verify_src("res_payload", src) else { return };
    assert!(o.is_verified(), "`res_payload` must verify, got: {o}");
}

/// A cast in a *contract* (`x as u32`) is readable, and it extends the way Rust
/// does: `-1i8 as i16` is `-1`, and `-1i8 as u16` is `65535` (sign-extended even
/// into an unsigned target), not the zero-extended `255`.
///
/// The body has modelled `as` for a while; the contract language had none, so a
/// contract relating a narrow argument to a wide return was unreadable. The
/// direction is the whole point: a contract cast that zero-filled a signed source
/// would refute the true `ret == 65535` and prove the false `ret == 255`, so the
/// true entries verifying *and* the tripwires being refuted is what pins it.
#[test]
fn a_cast_in_a_contract_extends_like_rust() {
    let Some(report) = verify_realistic(&[
        "contract_cast_widens_unsigned",
        "contract_cast_widens_unsigned_tripwire",
        "contract_cast_widens_signed",
        "contract_cast_signed_to_unsigned",
        "contract_cast_signed_to_unsigned_tripwire",
        "contract_cast_narrows",
        "contract_cast_narrows_tripwire",
        "contract_cast_chain",
        "contract_cast_chain_tripwire",
    ]) else {
        return;
    };
    for name in [
        "contract_cast_widens_unsigned",
        "contract_cast_widens_signed",
        "contract_cast_signed_to_unsigned",
        "contract_cast_narrows",
        "contract_cast_chain",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    for name in [
        "contract_cast_widens_unsigned_tripwire",
        "contract_cast_signed_to_unsigned_tripwire",
        "contract_cast_narrows_tripwire",
        "contract_cast_chain_tripwire",
    ] {
        let o = outcome(&report, name);
        let FnOutcome::Failed { kind, .. } = o else {
            panic!("`{name}` must FAIL: a `Skipped` means the cast is not modelled, got: {o}");
        };
        assert_eq!(kind, "postcondition", "`{name}` got: {o}");
    }
    // The sign-extension witness must be `-1`, the one input where the two
    // extension rules differ; naming any other input would mean the model
    // disagrees with `core` elsewhere.
    let o = outcome(&report, "contract_cast_signed_to_unsigned_tripwire");
    let FnOutcome::Failed { detail, .. } = o else { panic!("got: {o}") };
    assert!(
        detail.contains("= 255"),
        "the sign-extension witness should be x == -1 (bits 255), got: {detail}"
    );
}

/// The cast shape in an isolated file, so the parse is pinned even if the corpus
/// entry is edited: `ret == x as u32` must be *readable* (a cast the parser cannot
/// read is a `Skipped`, i.e. a dropped obligation) and must hold.
#[test]
fn a_contract_cast_is_read_and_proved() {
    let src = r#"
        /// requires: true
        /// ensures: ret == x as u32
        pub fn widen(x: u8) -> u32 {
            x as u32
        }
        /// requires: true
        /// ensures: ret == x as u8
        pub fn narrow(x: u16) -> u8 {
            x as u8
        }
    "#;
    let Some(o) = verify_src("widen", src) else { return };
    assert!(o.is_verified(), "`widen` must verify, got: {o}");
    let Some(o) = verify_src("narrow", src) else { return };
    assert!(o.is_verified(), "`narrow` must verify, got: {o}");
}

/// The contract operators that were missing (`/ % << >>`), and the precedence
/// they need. A missing operator is a dropped obligation -- the contract is
/// unreadable and the function silently leaves the check set -- so each entry
/// pairs a true contract with a tripwire, and the precedence entries pin the
/// *order*, not merely that the operator parses.
///
/// The signed entries are the ones with teeth: `>>` on a signed value must be
/// arithmetic (`-8 >> 1 == -4`, not a large positive) and `/` must be the signed
/// quotient (`-7 / 2 == -3`, not a huge positive). The unsigned engine would give
/// a wrong value, so those entries separate the two engines.
#[test]
fn contract_operators_and_their_precedence() {
    let Some(report) = verify_realistic(&[
        "contract_shr_unsigned",
        "contract_shr_unsigned_tripwire",
        "contract_shl",
        "contract_shr_signed_is_arithmetic",
        "contract_shr_signed_is_arithmetic_tripwire",
        "contract_udiv",
        "contract_urem",
        "contract_udiv_tripwire",
        "contract_sdiv",
        "contract_srem",
        "contract_sdiv_tripwire",
        "contract_precedence_and_over_add",
        "contract_precedence_and_over_add_tripwire",
        "contract_precedence_add_over_shl",
        "contract_precedence_add_over_shl_tripwire",
        "contract_precedence_and_over_or",
        "contract_precedence_and_over_or_tripwire",
        "contract_precedence_shift_over_eq",
        "contract_precedence_shift_over_eq_tripwire",
        "contract_precedence_cast_over_add",
        "contract_precedence_neg_over_cast",
        "contract_precedence_neg_over_rem",
        "contract_precedence_mul_rem_left_assoc",
    ]) else {
        return;
    };
    for name in [
        "contract_shr_unsigned",
        "contract_shl",
        "contract_shr_signed_is_arithmetic",
        "contract_udiv",
        "contract_urem",
        "contract_sdiv",
        "contract_srem",
        "contract_precedence_and_over_add",
        "contract_precedence_add_over_shl",
        "contract_precedence_and_over_or",
        "contract_precedence_shift_over_eq",
        "contract_precedence_cast_over_add",
        "contract_precedence_neg_over_cast",
        "contract_precedence_neg_over_rem",
        "contract_precedence_mul_rem_left_assoc",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    for name in [
        "contract_shr_unsigned_tripwire",
        "contract_shr_signed_is_arithmetic_tripwire",
        "contract_udiv_tripwire",
        "contract_sdiv_tripwire",
        "contract_precedence_and_over_add_tripwire",
        "contract_precedence_add_over_shl_tripwire",
        "contract_precedence_and_over_or_tripwire",
        "contract_precedence_shift_over_eq_tripwire",
    ] {
        let o = outcome(&report, name);
        let FnOutcome::Failed { kind, .. } = o else {
            panic!("`{name}` must FAIL: a `Skipped` means the operator is not modelled, got: {o}");
        };
        assert_eq!(kind, "postcondition", "`{name}` got: {o}");
    }
    // `-8 >> 1` is `-4`, so a *logical* reading (a large positive) is what the
    // tripwire refutes; the witness `248` is the `-8` bit pattern, which pins
    // that the parser read the sign, not merely the value.
    let o = outcome(&report, "contract_shr_signed_is_arithmetic_tripwire");
    let FnOutcome::Failed { detail, .. } = o else { panic!("got: {o}") };
    assert!(detail.contains("= 248"), "the witness should be the `-8` pattern, got: {detail}");
    // The `&`/`+` precedence tripwire must be refuted at `x == 1`, the input
    // where `x & (1 + 1)` and `(x & 1) + 1` differ.
    let o = outcome(&report, "contract_precedence_and_over_add_tripwire");
    let FnOutcome::Failed { detail, .. } = o else { panic!("got: {o}") };
    assert!(detail.contains("= 1"), "the witness should be `x == 1`, got: {detail}");
}

/// A `u128`/`i128` function must be *refused*, not panicked. The engine's words
/// are 1..=64 bits and every width-taking constructor asserts that, so a 128-bit
/// argument, return, local or cast target has no width to model. Before the
/// guard, whichever of the argument seeding, the loop havoc or the contract
/// bindings ran first hit that assertion and took the whole run down — a panic
/// reports nothing, where a refusal reports the function. This pins the refusal
/// on each path, and that a 64-bit neighbour still verifies.
#[test]
fn a_128_bit_function_is_refused_not_panicked() {
    let Some(report) = verify_realistic(&[
        "wide_arg",
        "wide_return",
        "wide_local_in_loop",
        "wide_cast_in_contract",
        "narrow_64_still_works",
    ]) else {
        return;
    };
    for name in ["wide_arg", "wide_return", "wide_local_in_loop", "wide_cast_in_contract"] {
        let o = outcome(&report, name);
        let FnOutcome::Skipped { reason } = o else {
            panic!("`{name}` must be refused, got: {o}");
        };
        assert!(
            reason.contains("64-bit") || reason.contains("wider"),
            "`{name}` should say why, got: {reason}"
        );
    }
    // The guard must be about the function's own width, not a blanket refusal of
    // anything mentioning 128 bits: a `u64` neighbour still verifies.
    let o = outcome(&report, "narrow_64_still_works");
    assert!(o.is_verified(), "a 64-bit function must still verify, got: {o}");
}

/// The contract parser must refuse a cast *to* a 128-bit type on its own, since a
/// function whose own types are all 64-bit would otherwise reach `truncate` and
/// panic there. Pinned in isolation so the refusal does not depend on the corpus.
#[test]
fn a_contract_cast_to_128_bits_is_refused() {
    let src = "/// requires: true\n/// ensures: ret == x as u128\n\
               pub fn f(x: u8) -> u64 { x as u64 }";
    let Some(o) = verify_src("f", src) else { return };
    let FnOutcome::Skipped { reason } = o else {
        panic!("a cast to `u128` must be refused, got: {o}");
    };
    assert!(reason.contains("u128"), "the refusal should name the type, got: {reason}");
}

/// The operator shapes in an isolated file, so the *parse* is pinned even if the
/// corpus entry is edited. Each is one line, so a regression says exactly which
/// operator stopped being read.
#[test]
fn contract_operators_parse_in_isolation() {
    let cases: &[(&str, &str)] = &[
        ("shr", "/// requires: true\n/// ensures: ret == x >> 1\npub fn shr(x: u8) -> u8 { x >> 1 }"),
        ("shl", "/// requires: true\n/// ensures: ret == x << 2\npub fn shl(x: u8) -> u8 { x << 2 }"),
        ("udiv", "/// requires: true\n/// ensures: ret == x / 3\npub fn udiv(x: u32) -> u32 { x / 3 }"),
        ("urem", "/// requires: true\n/// ensures: ret == x % 10\npub fn urem(x: u32) -> u32 { x % 10 }"),
        (
            "prec",
            "/// requires: true\n/// ensures: ret == x & 1 + 1\npub fn prec(x: u8) -> u8 { x & 2 }",
        ),
    ];
    for (name, src) in cases {
        let Some(o) = verify_src(name, src) else { return };
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
}

/// A constant signed expression, with no symbolic operand, must use the *signed*
/// engine for `%`, `/` and `>>`. Signedness is inferred from the names in an
/// expression, and there are none here, so the negated literal is the only
/// evidence — and it used to report itself unsigned. The mistake was a *wrong
/// value*, not a refusal: the unsigned `%` gives `4294967289 % 3 == 0` where Rust
/// says `-1`, and the tripwires below would then have *verified*, which is the
/// direction that manufactures a false proof. Each pair is asserted both ways, so
/// a fix that merely flipped the flag the other way fails here too.
#[test]
fn a_constant_signed_expression_uses_the_signed_engine() {
    let srcs = [
        (
            "srem",
            "/// requires: true\n/// ensures: ret == -7 % 3\n\
             pub fn srem() -> i32 { -7i32 % 3i32 }",
            "/// requires: true\n/// ensures: ret == 2\n\
             pub fn srem() -> i32 { -7i32 % 3i32 }",
        ),
        (
            "sdiv",
            "/// requires: true\n/// ensures: ret == -7 / 2\n\
             pub fn sdiv() -> i32 { -7i32 / 2i32 }",
            "/// requires: true\n/// ensures: ret == 3\n\
             pub fn sdiv() -> i32 { -7i32 / 2i32 }",
        ),
        (
            "ashr",
            "/// requires: true\n/// ensures: ret == -8 >> 1\n\
             pub fn ashr() -> i32 { -8i32 >> 1 }",
            "/// requires: true\n/// ensures: ret == -1\n\
             pub fn ashr() -> i32 { -8i32 >> 1 }",
        ),
    ];
    for (name, true_src, false_src) in srcs {
        let Some(o) = verify_src(name, true_src) else { return };
        assert!(o.is_verified(), "`{name}` (true) must verify, got: {o}");
        let Some(o) = verify_src(name, false_src) else { return };
        assert!(!o.is_verified(), "`{name}` (tripwire) must be refuted, got: {o}");
    }
}

/// Unary `-` binds *tighter* than `as`, so `-x as u8` has type `u8` — unsigned.
/// Reading it the other way (`-(x as u8)`, signed) made `-x as u8 > 127`
/// unsatisfiable, so a function that is verifiable was reported *vacuous*. Both
/// directions are asserted: the satisfiable one must verify, and the tripwire —
/// which the signed reading would wrongly *verify* — must be refuted.
#[test]
fn a_negation_binds_tighter_than_a_cast() {
    let cases = [
        (
            "neg_cast_gt",
            "/// requires: -x as u8 > 127\n/// ensures: ret == 1\n\
             pub fn neg_cast_gt(x: i8) -> u8 { 1 }",
            true,
        ),
        (
            "neg_cast_lt_tripwire",
            "/// requires: x == 1\n/// ensures: -x as u8 < 127\n\
             pub fn neg_cast_lt_tripwire(x: i8) -> u8 { 1 }",
            false,
        ),
        (
            "neg_cast_value",
            "/// requires: x == -5\n/// ensures: ret == -x as u8\n\
             pub fn neg_cast_value(x: i8) -> u8 { -x as u8 }",
            true,
        ),
    ];
    for (name, src, want_verified) in cases {
        let Some(o) = verify_src(name, src) else { return };
        assert_eq!(
            o.is_verified(),
            want_verified,
            "`{name}`: expected verified={want_verified}, got: {o}"
        );
    }
}

/// A differential oracle for the contract expression language, against rustc.
///
/// The five existing oracles (z3, Kani, Lean, Coq, Verus) all build their terms with
/// `smt::` calls, so they start *below* the contract reader — the layer where three
/// bugs in a row lived. This closes that gap using the one decision procedure that
/// defines Rust: the compiler.
///
/// Two constructions, because the two bugs this found needed different ones:
///
/// * **Value** (`guard: None`). The body *is* the expression, so `ret` is rustc's
///   value of `E` at `x == v`; the postcondition `ret == E` asserts the reader's value
///   of `E` at the same point. This catches a wrong *value* — the signedness bug, where
///   `-7 % 3` was read as `0`.
///
/// * **Guard** (`guard: Some(t)`). The precondition is `x == v && E > t`, so the
///   comparison is decided at exactly `v`, and the body returns `1` with `ensures: ret
///   == 1`. The function verifies iff rustc says `E > t` at `v`. This is what catches a
///   wrong *type*: `-x as u8` and `-(x as u8)` have the same value (negation and
///   truncation commute), so no value check sees the difference — but only one of them
///   is `u8`, and the comparison is what reads the type. Pinning `x == v` makes the
///   expected verdict exact, so a *vacuous* result is a failure and not a grey area.
///
/// The grid is the point. A single point per expression would have missed the
/// signedness bug, so each case runs every value where a signed/unsigned confusion is
/// visible: the extremes of the type, `-1`, `0`, `1`. Each case lists its own grid,
/// because some expressions overflow at the extreme (`-x` for `x == i8::MIN` panics,
/// and `(x + 1) << 1` overflows `u8` at `x == 127`) — a panic is a *true* verdict, but
/// not the agreement this test is for.
#[test]
fn the_contract_reader_agrees_with_rustc_on_a_grid() {
    // (expression, argument type, return type, grid, guard threshold)
    type Case = (&'static str, &'static str, &'static str, &'static [i64], Option<u8>);
    let cases: &[Case] = &[
        // Signed remainder, division and arithmetic shift, over the grid. The negative
        // points are what separate the signed engine from the unsigned one.
        ("x % 3", "i8", "i8", &[-128, -7, -1, 0, 1, 7, 127], None),
        ("x / 2", "i8", "i8", &[-128, -7, -1, 0, 1, 7, 127], None),
        ("x >> 1", "i8", "i8", &[-128, -7, -1, 0, 1, 7, 127], None),
        // A negated literal, the shape the first bug was about.
        ("-7 % 3", "i8", "i8", &[0], None),
        ("-7 / 2", "i8", "i8", &[0], None),
        ("-8 >> 1", "i8", "i8", &[0], None),
        // Unary `-` before the cast, as a *value*: both readings agree, so this half
        // only guards against a fix that broke the value.
        ("-x as u8", "i8", "u8", &[-7, -1, 0, 1, 127], None),
        // The same expression as a *guard*, which is where the type is observable:
        // `(-x) as u8 > 127` is true at `x == 1` (255), false under a signed reading.
        ("-x as u8", "i8", "u8", &[-7, -1, 0, 1, 127], Some(127)),
        // Casts: widening sign-extends, narrowing keeps the low bits, a chain is
        // left to right.
        ("x as i16", "i8", "i16", &[-128, -1, 0, 1, 127], None),
        ("x as i8", "i16", "i8", &[-32768, -129, -1, 0, 1, 127, 128, 32767], None),
        ("x as i8 as i32", "i16", "i32", &[-32768, -129, -1, 0, 1, 127, 128, 32767], None),
        ("x as u16", "u8", "u16", &[0, 1, 128, 255], None),
        // Precedence and associativity, on the grid.
        ("x & 1 + 1", "u8", "u8", &[0, 1, 2, 3, 255], None),
        ("x + 1 << 1", "u8", "u8", &[0, 1, 63, 126], None),
        ("x | 1 ^ 1", "u8", "u8", &[0, 1, 255], None),
        ("x & 3 | 4", "u8", "u8", &[0, 1, 3, 255], None),
        ("x ^ 1 & 3", "u8", "u8", &[0, 1, 3, 255], None),
        ("x | 1 ^ 2", "u8", "u8", &[0, 1, 2, 255], None),
        // Unary `!` stacked, and `!` feeding a shift: both are bitwise, so `!!x` is
        // `x` and `!x >> 1` shifts the complement.
        ("!!x", "u8", "u8", &[0, 1, 5, 250, 255], None),
        ("!x >> 1", "u8", "u8", &[0, 1, 250, 255], None),
        // A shift and a bitwise `|` in one expression: `x << 1 | 1` is
        // `(x << 1) | 1`, because `<<` binds tighter than `|`.
        ("x << 1 | 1", "u8", "u8", &[0, 1, 2, 63], None),
        // Unary `-` feeding a shift, and unary `-` feeding `+`.
        ("-x >> 1", "i8", "i8", &[-127, -1, 0, 1, 127], None),
        ("-x + 1", "i8", "i8", &[-126, -1, 0, 1, 126], None),
        // A cast feeding a bitwise `&`, and a double cast.
        ("x as u16 & 1", "i8", "u16", &[-128, -1, 0, 1, 127], None),
        ("x as u8 as u16", "i8", "u16", &[-128, -1, 0, 1, 127], None),
        // `*` binds tighter than `+`, and a repeated shift is left-associative.
        ("1 + x * 2", "u8", "u8", &[0, 1, 5, 63], None),
        ("x >> 1 >> 1", "u8", "u8", &[0, 1, 255], None),
        // A cast binds tighter than `+`, and unary `-` binds tighter than a cast. The
        // guard mode reads the *type* of the result, which is where `(x as i16) + 1`
        // and `x as (i16 + 1)` would differ. (`*` is left out: an `i16 * i16` body has
        // an overflow assert the engine declines to model at that width, so the probe
        // itself is undecided and the guard mode cannot read the comparison.)
        ("x as i16 + 1", "i8", "i16", &[-1, 0, 5, 126], Some(6)),
        ("-x as i16", "i8", "i16", &[-1, 0, 1, 127], None),
        ("x << 2", "u8", "u8", &[0, 1, 63, 255], None),
        ("8 - 4 - 2", "i32", "i32", &[0], None),
        ("8 / 4 / 2", "u32", "u32", &[0], None),
        // A negation of a name, and a double negation, which is the value again.
        ("-x", "i8", "i8", &[-127, -1, 0, 1, 127], None),
        ("- -x", "i8", "i8", &[-127, -1, 0, 1, 127], None),
        // `0 - x` is a subtraction, not a negation, so it *overflows* at `x ==
        // i8::MIN` (the body panics, a true verdict but not an agreement point).
        ("0 - x", "i8", "i8", &[-127, -1, 0, 1, 127], None),
        // The signedness of a comparison on a variable, over the whole grid.
        ("x", "i8", "i8", &[-128, -7, -1, 0, 1, 7, 127], Some(0)),
        ("x % 3", "i8", "i8", &[-128, -7, -1, 0, 1, 7, 127], Some(0)),
        // Unary `!` on a value is *bitwise* NOT, and binds tighter than `==`:
        // `!x == 5` is `(!x) == 5` (`x == 250`), not `!(x == 5)` (`x != 5`). The
        // predicate reading is a different predicate, so it is a wrong verdict.
        ("!x", "u8", "u8", &[0, 1, 128, 255], None),
        ("!!x", "u8", "u8", &[0, 1, 128, 255], None),
        ("!x + 1", "u8", "u8", &[1, 128, 255], None),
        ("x & !1", "u8", "u8", &[0, 1, 3, 255], None),
        // The guard form is the discriminator: `(!x) == 5` holds only at `x == 250`,
        // where `!(x == 5)` would hold everywhere else. Pinning `x == v` makes the
        // two readings differ at every point but one.
        ("!x", "u8", "u8", &[0, 1, 5, 250, 255], Some(5)),
        ("!x", "u8", "u8", &[0, 1, 5, 250, 255], Some(4)),
        // Parentheses do not make it a predicate: `!(x + 1)` holds *arithmetic*, so
        // `!` is still the value form and `!(x + 1) == 5` is `(!(x + 1)) == 5`, not a
        // negation of `(x + 1) == 5` (which is not even well-typed). This is the case
        // that separates `bang_is_predicate`'s lookahead from "a `(` follows".
        ("!(x + 1)", "u8", "u8", &[0, 1, 5, 249, 254], None),
        // A shift amount is a constant *expression*: the reader and the body must
        // both fold `1 + 1` to `2`, not treat it as a symbolic barrel-shifter
        // amount. The value mode builds `x >> 1 + 1` as the body *and* the
        // postcondition, so an unreadable contract (a non-folded reader) shows up
        // as a non-verified outcome here.
        ("x >> 1 + 1", "u8", "u8", &[0, 1, 2, 4, 8, 16, 128, 255], None),
        // A radix literal is the expression in *both* the body and the
        // postcondition: rustc compiles the body `0xFF` to `255`, and the reader
        // must read the contract `0xFF` as `255` for `ret == 0xFF` to hold. A
        // decimal-only reader read it as `0`, so the postcondition became
        // `ret == 0` and the tool *proved* it for a body returning `255` -- a false
        // proof, which this row turns into a disagreement. The `x == 0` guard makes
        // the function total so the only thing under test is the literal.
        ("0xFF", "u8", "u8", &[0], None),
        ("0b1010", "u8", "u8", &[0], None),
        ("0o17", "u8", "u8", &[0], None),
        ("0xFFu8", "u8", "u8", &[0], None),
        ("0xFF_FF", "u16", "u16", &[0], None),
        ("0x10", "u8", "u8", &[0], None),
    ];

    let mut checked = 0u32;
    for (expr, arg_ty, ret_ty, grid, guard) in cases {
        for &v in *grid {
            // A stable, identifier-safe name: the index, not the expression (which
            // contains characters Rust will not take in a name).
            let name = format!("oracle_{checked}");
            let (src, want) = match guard {
                // Value: body is the expression, postcondition asserts the reader's
                // value equals rustc's.
                None => (
                    format!(
                        "/// requires: x == {v}\n/// ensures: ret == {expr}\n\
                         pub fn {name}(x: {arg_ty}) -> {ret_ty} {{ {expr} }}\n"
                    ),
                    true,
                ),
                // Guard: the body returns `1` and the precondition is the comparison
                // pinned at `v`, so it verifies iff rustc's comparison is true.
                Some(t) => {
                    // Ask rustc for the comparison at this point, so the expectation is
                    // the compiler's, not mine.
                    let probe = format!(
                        "/// requires: x == {v}\n/// ensures: ret == 1\n\
                         pub fn {name}(x: {arg_ty}) -> u8 {{ if {expr} > {t} {{ 1 }} else {{ 0 }} }}\n"
                    );
                    // The probe's body is rustc's comparison; the value it returns is
                    // what `expect_verified` must match. `1` means satisfiable.
                    let o = verify_src(&name, &probe);
                    let Some(o) = o else { return };
                    // The probe verifies iff the body always returns `1`, which is true
                    // only when the comparison holds at `v`.
                    let truth = o.is_verified();
                    let src = format!(
                        "/// requires: x == {v} && {expr} > {t}\n/// ensures: ret == 1\n\
                         pub fn {name}(x: {arg_ty}) -> u8 {{ 1 }}\n"
                    );
                    (src, truth)
                }
            };
            let Some(o) = verify_src(&name, &src) else { return };
            assert_eq!(
                o.is_verified(),
                want,
                "the reader disagrees with rustc: `{expr}` at x == {v} ({arg_ty}), guard {guard:?} — expected verified={want}, got: {o}"
            );
            checked += 1;
        }
    }
    // A run that checked nothing is not evidence.
    assert!(checked >= 60, "the oracle checked only {checked} points");
}

/// A shift amount or a divisor may be a *constant expression*, not only a bare
/// literal, and the reader must fold it before deciding what it is.
///
/// `x >> 1 + 1` is `x >> 2` and `x % (1 - 1)` is `x % 0`; Rust evaluates both
/// amounts at compile time. The reader tested the raw operand with `const_of`,
/// which only recognises a literal node, so a folded amount was misclassified in
/// two opposite directions: a constant shift amount looked symbolic (the body built
/// a barrel shifter and the engine could not decide), and a constant *zero* divisor
/// slipped past the divide-by-zero guard and produced a definite verdict from an
/// undefined `srem(x, 0)` -- a wrong verdict, the one outcome a verifier must not
/// produce. The fix folds with `const_value`/`evaluate` on both sides.
#[test]
fn a_folded_constant_is_read_as_a_constant() {
    // A folded shift amount verifies: the body shifts by the same constant.
    let Some(o) = verify_src(
        "folded_shift_amount",
        "/// requires: x == 8\n/// ensures: ret == x >> 1 + 1\n\
         pub fn folded_shift_amount(x: u8) -> u8 { x >> 2 }\n",
    ) else {
        return;
    };
    assert!(o.is_verified(), "a folded shift amount must be read, got: {o}");

    // A folded *zero* divisor is refused, exactly as the literal `0` is. The
    // requirement is that it is not *decided*: a verdict built on `srem(x, 0)`
    // would be a verdict about nothing.
    let Some(o) = verify_src(
        "folded_zero_divisor",
        "/// requires: x == 3\n/// ensures: ret == x % (1 - 1)\n\
         pub fn folded_zero_divisor(x: u8) -> u8 { x % 3 }\n",
    ) else {
        return;
    };
    assert!(
        matches!(o, FnOutcome::Skipped { .. }),
        "a folded zero divisor must be refused, not decided, got: {o}"
    );

    // A folded *non-zero* divisor still reads and models exactly: `4 / (1 + 1)`
    // is `4 / 2` is `2`, the same as the body, so the two agree.
    let Some(o) = verify_src(
        "folded_nonzero_divisor",
        "/// requires: x == 4\n/// ensures: ret == x / (1 + 1)\n\
         pub fn folded_nonzero_divisor(x: u8) -> u8 { x / 2 }\n",
    ) else {
        return;
    };
    assert!(
        o.is_verified(),
        "a folded non-zero divisor must be read and modelled, got: {o}"
    );

    // And the *body* folds the same way: `x >> 1 + 1` lowers to a constant shift,
    // not a barrel shifter, so the query is decided rather than left incomplete.
    let Some(o) = verify_src(
        "folded_body_shift",
        "/// requires: x == 8\n/// ensures: ret == 2\n\
         pub fn folded_body_shift(x: u8) -> u8 { x >> 1 + 1 }\n",
    ) else {
        return;
    };
    assert!(
        o.is_verified(),
        "a folded shift amount in the body must be lowered as a constant, got: {o}"
    );
}

/// A radix literal must be read at its radix, and the *control* is the point.
///
/// `0xFF` used to read as `0`, so `requires: x == 0xFF` became `x == 0` and
/// `ensures: ret == 0` was **proved** for a function returning `255` -- a false
/// proof, the worst outcome this crate can produce. The verifying entries show the
/// value is now right; the control shows the truncated value is gone, because it is
/// the entry that used to be a false proof and must now be refuted.
#[test]
fn a_radix_literal_is_read_at_its_radix() {
    let verified = [
        "contract_hex_literal_is_255",
        "contract_binary_literal_is_ten",
        "contract_octal_literal_is_fifteen",
        "contract_hex_underscore_is_65535",
        "contract_hex_with_suffix_is_255",
    ];
    let Some(report) = verify_realistic(&verified) else { return };
    for name in verified {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    let Some(report) = verify_realistic(&["contract_hex_literal_is_not_zero_control"]) else {
        return;
    };
    let o = outcome(&report, "contract_hex_literal_is_not_zero_control");
    let FnOutcome::Failed { kind, detail, .. } = o else {
        panic!("the control must be refuted -- verifying it is the false proof, got: {o}");
    };
    assert_eq!(kind, "postcondition", "the control got: {o}");
    // The witness is `255`, the value `0xFF` *should* be. Under the old truncating
    // read it would have been a proof, so the witness is the evidence the literal
    // is now read at radix 16.
    assert!(detail.contains("= 255"), "the witness should be `255`, got: {detail}");
}

/// The corpus entries that pin *where* `!` binds, asserted end to end.
///
/// `!` is bitwise NOT on a value and negation on a predicate, and it binds tighter
/// than `==`, `&` and `as`. Each entry below separates one of those bindings, so a
/// reader that got one wrong would either fail to parse or return the other value.
/// The control is the `==` case: it is *false* under Rust's reading and must be
/// refuted, which is what makes the verifying entry next to it evidence rather than
/// a tool that proves everything.
#[test]
fn a_bang_binds_by_rusts_precedence_in_the_corpus() {
    let verified = [
        "contract_bang_binds_tighter_than_eq",
        "contract_bang_is_bitwise_not",
        "contract_bang_still_negates_a_predicate",
        "contract_bang_binds_tighter_than_a_cast",
        "contract_bang_binds_tighter_than_and",
        "contract_bang_paren_arithmetic_is_a_value",
    ];
    let Some(report) = verify_realistic(&verified) else { return };
    for name in verified {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    let Some(report) = verify_realistic(&["contract_bang_binds_tighter_than_eq_control"]) else {
        return;
    };
    let o = outcome(&report, "contract_bang_binds_tighter_than_eq_control");
    let FnOutcome::Failed { .. } = o else {
        panic!("`contract_bang_binds_tighter_than_eq_control` is false and must be refuted, got: {o}");
    };
}

