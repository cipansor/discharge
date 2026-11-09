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
fn sat_mul_is_verified_by_the_exact_division_overflow_test() {
    let Some(report) = verify_all() else { return };
    let o = outcome(&report, "sat_mul");
    // `sat_mul` guards `a * b` with `b != 0 && a > u16::MAX / b`. That guard *is* the
    // exact unsigned multiply-overflow predicate, so the path into the multiply
    // refutes the overflow obligation -- no 32-bit product is built, and the widened
    // product that used to be the documented BDD wall is never posed.
    //
    // This was `Incomplete` before, for a reason worth keeping visible: the predicate
    // used to be `x > MAX / c` only for a *constant* operand, and the general path
    // widened to `2w` bits and refused past 16. The two obligations were then
    // `b == 0 && a <= MAX / b` (path) against `b != 0 && a > MAX / b` (overflow), which
    // cancel pairwise but only *across* two `&&` spines -- so the boolean fold has to
    // see through the spines for the query to close. Both halves are what this test
    // pins: the exact division predicate, and the spine-aware cancellation that lets it
    // fold against the guard.
    assert!(
        o.is_verified(),
        "sat_mul must be verified now that the multiply-overflow test is exact: {o}"
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

/// Deliberately runs on the *default* test-thread stack (2 MiB), not a worker with
/// a larger one.
///
/// The corpus contains a nested shift amount (`x >> ((2 << 7) + 1)`), and the
/// parser recurses once per nesting level, so this call is sensitive to the size of
/// a parser frame. It used to abort here: `smt::evaluate` owns a 12 KiB memo as a
/// stack local, the optimiser inlined it into the recursive parser, and every level
/// of nesting then cost 12 KiB of stack. The fix is `#[inline(never)]` on
/// `evaluate` (see its doc comment), which brings the parse depth to ~15 KiB. This
/// test is the *gate* on that: reverting the attribute re-inflates the frames and
/// this aborts, so the fix cannot be quietly undone. A 64 MiB worker thread here
/// would have hidden the bug instead of catching it.
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

/// A contract can name a *tuple struct's* field, numbered by position.
///
/// `struct_head` recognised only a braced body, so `pub struct Pair(pub u8, pub u8)`
/// was never read as a struct at all: the argument's type stayed an opaque
/// `Other("Pair")` with no layout, and a contract naming `p.0` was refused as
/// "unknown name `p`". The positional index *is* the MIR field index, so `p.0` and
/// the body's `(*_1).0` must name one variable -- and each field must be its own
/// input, not one aliased word.
///
/// The four verdicts pin the four things that could go wrong: the read itself
/// (`verified`), the read through a reference as well as by value (`verified`),
/// the declared *signedness* of the field (`verified`, and only under the signed
/// reading), and the independence of the two fields (`FAILED`, which is the
/// evidence they are distinct -- one shared variable would make the contract hold).
#[test]
fn a_contract_can_name_a_tuple_struct_field() {
    let Some(report) = verify_realistic(&[
        "tuple_struct_reads_its_field",
        "tuple_struct_by_value_reads_its_field",
        "tuple_struct_signed_field_reads",
        "tuple_struct_fields_are_independent",
    ]) else {
        return;
    };
    for name in [
        "tuple_struct_reads_its_field",
        "tuple_struct_by_value_reads_its_field",
        "tuple_struct_signed_field_reads",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must be read and verified; got: {o}");
    }
    let o = outcome(&report, "tuple_struct_fields_are_independent");
    assert!(
        !o.is_verified(),
        "`tuple_struct_fields_are_independent` must be refuted -- a reader that aliased \
         `p.0` and `p.1` to one variable would prove it; got: {o}"
    );
}

/// A tuple field the layout does not have is refused, and so is a *nested* path
/// that walks off the layout.
///
/// `Pair` has two fields, so `p.2` names nothing. Binding it to a fabricated word
/// would let a contract about a field that does not exist be proved, which is a
/// false proof rather than a missing one. `n.p.q` is the nested form: `n.p` *is*
/// bound (it is a `Pair` with a layout), but `Pair` has no field `q`, so the walk
/// stops and the path is refused -- naming the segment that failed, not the whole
/// path. Both refusals are the safe direction, and this pins them.
#[test]
fn a_tuple_struct_field_that_does_not_exist_is_refused() {
    let Some(report) = verify_realistic(&[
        "tuple_struct_out_of_range_field_is_refused",
        "nested_path_off_the_layout_is_refused",
    ]) else {
        return;
    };
    for name in [
        "tuple_struct_out_of_range_field_is_refused",
        "nested_path_off_the_layout_is_refused",
    ] {
        let o = outcome(&report, name);
        assert!(
            !o.is_verified(),
            "`{name}` names a field the layout does not have and must be refused; got: {o}"
        );
    }
}

/// A *nested* field projection is read: the contract's `n.p.0` and the body's
/// `(((*_1).0).0)` are one input.
///
/// This is the coverage the nested support adds. `n.p.0` is a walk of two field
/// projections, and the single-field store would answer it by looking up the
/// *outer* field `(local, 0)` twice -- returning `n.p` for `n.p.0`, a wrong value
/// rather than a missing one. The positive entry pins that the contract and the
/// body agree; the false entry pins that a disagreeing postcondition is refuted,
/// so the agreement is not vacuous.
#[test]
fn a_nested_field_projection_is_read_and_agrees_with_the_body() {
    let Some(report) = verify_realistic(&[
        "nested_tuple_projection_reads",
        "nested_tuple_projection_is_the_body_value",
        "nested_named_field_reads_its_leaf",
        "nested_named_field_is_the_body_value",
    ]) else {
        return;
    };
    for name in [
        "nested_tuple_projection_reads",
        "nested_tuple_projection_is_the_body_value",
        "nested_named_field_reads_its_leaf",
        "nested_named_field_is_the_body_value",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
}

/// Two nested leaves are *independent* inputs, which is what makes the binding a
/// walk rather than a single field.
///
/// The entries are toothed: each claims a value the body does not return, so a
/// reader that aliased the leaves (`n.p.0` with `n.p.1`, or `o.i.v` with `o.j.v`)
/// would *verify* them -- a false proof. Refuted is the evidence the leaves are
/// distinct, and each counterexample names two different variables, which is the
/// same evidence at the term level.
#[test]
fn nested_leaves_under_different_paths_are_independent() {
    let Some(report) = verify_realistic(&[
        "nested_tuple_projection_leaves_are_independent",
        "nested_named_leaves_under_different_fields",
    ]) else {
        return;
    };
    for name in [
        "nested_tuple_projection_leaves_are_independent",
        "nested_named_leaves_under_different_fields",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "`{name}` must be refuted: aliasing its leaves would make it a false proof; got: {o}"
        );
    }
}

/// A field write through a `&mut` is applied, not dropped -- and the *false*
/// direction is refuted rather than proved.
///
/// This is the regression for the two-sided soundness bug: `((*_1).0) = v` (a
/// `Deref` then a `Field`) had no arm in the store and fell to the drop arm. The
/// true entry pins that the write lands (the read after it is `5`); the false entry
/// pins that the postcondition is checked against the written value, so a contract
/// the body cannot satisfy is refuted instead of proved. Dropping the write makes
/// the false entry *verify* and the true entry fail, so both directions are toothed.
#[test]
fn a_field_write_through_a_mutable_reference_is_applied() {
    let Some(report) = verify_realistic(&[
        "field_write_through_ref_mut_takes_effect",
        "field_write_through_ref_mut_is_not_dropped",
    ]) else {
        return;
    };
    let true_dir = outcome(&report, "field_write_through_ref_mut_takes_effect");
    assert!(
        true_dir.is_verified(),
        "the write must land, so the read after it is 5; got: {true_dir}"
    );
    let false_dir = outcome(&report, "field_write_through_ref_mut_is_not_dropped");
    assert!(
        matches!(false_dir, FnOutcome::Failed { .. }),
        "the postcondition must be checked against the written value, so `ret == 0` \
         is refuted rather than proved; got: {false_dir}"
    );
}

/// A *nested* write through a `&mut` lands where the nested read looks, and the
/// false direction is refuted rather than proved.
///
/// The nested store is keyed by the whole chain, so `o.i.v = 5` and the later
/// `o.i.v` meet in one entry. A write keyed by a single field index would land on
/// the *outer* field and the read would see the caller's value: the true entry
/// would fail and the false entry would *verify*. Both are toothed here.
#[test]
fn a_nested_field_write_through_a_mutable_reference_is_applied() {
    let Some(report) = verify_realistic(&[
        "nested_field_write_through_ref_mut_takes_effect",
        "nested_field_write_through_ref_mut_is_not_dropped",
    ]) else {
        return;
    };
    let true_dir = outcome(&report, "nested_field_write_through_ref_mut_takes_effect");
    assert!(true_dir.is_verified(), "the nested write must land; got: {true_dir}");
    let false_dir = outcome(&report, "nested_field_write_through_ref_mut_is_not_dropped");
    assert!(
        matches!(false_dir, FnOutcome::Failed { .. }),
        "the nested write must be seen by the read, so `ret == 0` is refuted; got: {false_dir}"
    );
}

/// A seeded nested path is invalidated by a write that replaces the value it was
/// part of, and carried across by a whole-struct copy.
///
/// Both are the "parts" rules one level down. `o.i = Inner { v: 9 }` makes the seed
/// for `o.i.v` stale, so the false entry must be *refuted*: the body returns 9, and
/// `ret == 3` holds for no input. Refutation and not merely "not proved" is the
/// assertion, because a refusal also satisfies "not proved" and says nothing about
/// whether the write landed. The body lowers to a struct literal into a temp
/// followed by `(_1.0) = move _2`, so reaching the refutation is the evidence the
/// temp's parts were re-rooted under the destination's nested place.
///
/// And `c = d` must move `c.i.v` with the copy, so the true entry verifies -- it
/// pins `c.i.v` and `d.i.v` to different values, so `verified` is the evidence the
/// copy moved the right one rather than leaving `c`'s own seed.
#[test]
fn a_nested_seed_is_invalidated_by_a_write_and_carried_by_a_copy() {
    let Some(report) = verify_realistic(&[
        "whole_inner_write_makes_nested_seed_stale",
        "whole_inner_write_is_seen_by_the_leaf",
        "whole_inner_write_through_a_mutable_reference_is_seen",
        "whole_inner_move_carries_the_source_leaf",
        "whole_inner_move_is_not_the_stale_destination",
        "nested_swap_carries_the_other_side",
        "nested_swap_is_not_the_stale_side",
        "nested_aggregate_argument_reaches_the_helper",
        "nested_aggregate_argument_is_not_the_stale_destination",
        "nested_return_carries_the_field",
        "nested_return_is_not_the_stale_field",
        "whole_struct_copy_carries_nested_paths",
    ]) else {
        return;
    };
    let stale = outcome(&report, "whole_inner_write_makes_nested_seed_stale");
    assert!(
        matches!(stale, FnOutcome::Failed { .. }),
        "a stale nested seed must let the false contract be refuted, not refused; got: {stale}"
    );
    // The positive direction: the same body's true contract (`ret == 9`) verifies, so
    // the refutation above is the write landing and not a blanket refusal. Without this
    // pair, an engine that answered `Unknown` for the whole shape would pass.
    let landed = outcome(&report, "whole_inner_write_is_seen_by_the_leaf");
    assert!(
        landed.is_verified(),
        "a nested aggregate write must land where the leaf reads it; got: {landed}"
    );
    // The `&mut` companion: the same write's destination carries a leading deref, so the
    // re-rooting must resolve it or the field path never matches the read.
    let via_ref = outcome(&report, "whole_inner_write_through_a_mutable_reference_is_seen");
    assert!(
        via_ref.is_verified(),
        "a nested aggregate write through a &mut must reach the target's field path; got: {via_ref}"
    );
    let copy = outcome(&report, "whole_struct_copy_carries_nested_paths");
    assert!(copy.is_verified(), "a whole-struct copy must carry nested paths; got: {copy}");
    // A nested-to-nested move: the *source* is a projection, which `copy_parts` refuses, so
    // the re-rooting has to run on a nested source too. The pair pins both directions -- the
    // source's leaf arrives (true `ret == 3`), and the destination's stale leaf is gone (the
    // false `ret == 7` is refuted rather than proved against the seed the move replaced).
    let carried = outcome(&report, "whole_inner_move_carries_the_source_leaf");
    assert!(
        carried.is_verified(),
        "a nested-to-nested move must carry the source's leaf; got: {carried}"
    );
    let stale_move = outcome(&report, "whole_inner_move_is_not_the_stale_destination");
    assert!(
        matches!(stale_move, FnOutcome::Failed { .. }),
        "the destination's pre-move leaf must not survive the move; got: {stale_move}"
    );
    // A nested swap: both sides are nested, so this is the shape that needs the guard to be
    // "either side nested". The two seeds are distinct, so the positive verdict is the
    // *other* side's leaf, and the twin claims the pre-swap one survived.
    let swap = outcome(&report, "nested_swap_carries_the_other_side");
    assert!(swap.is_verified(), "a nested swap must exchange the leaves; got: {swap}");
    let swap_stale = outcome(&report, "nested_swap_is_not_the_stale_side");
    assert!(
        matches!(swap_stale, FnOutcome::Failed { .. }),
        "a nested swap must not keep each side's own leaf; got: {swap_stale}"
    );
    // A nested aggregate handed to a helper by value and read back: the callee's return is a
    // struct it built field-by-field, so the merge has to carry the *fields* (not only the
    // tuple components). The positive verdict is the value that crossed; the twin claims a
    // different one survived and must be refuted.
    let through = outcome(&report, "nested_aggregate_argument_reaches_the_helper");
    assert!(
        through.is_verified(),
        "a returned nested aggregate must keep its fields; got: {through}"
    );
    let through_stale =
        outcome(&report, "nested_aggregate_argument_is_not_the_stale_destination");
    assert!(
        matches!(through_stale, FnOutcome::Failed { .. }),
        "a returned nested aggregate must not keep a stale field; got: {through_stale}"
    );
    // A returned struct's *field* read back through a two-level path: the `Struct` literal
    // stores the field value but not the operand aggregate's own parts, so the field's parts
    // have to be re-rooted. The positive verdict is the value that crossed; the twin claims a
    // different leaf and must be refuted.
    let field = outcome(&report, "nested_return_carries_the_field");
    assert!(
        field.is_verified(),
        "a returned struct's field must keep its parts; got: {field}"
    );
    let field_stale = outcome(&report, "nested_return_is_not_the_stale_field");
    assert!(
        matches!(field_stale, FnOutcome::Failed { .. }),
        "a returned struct's field must not keep a stale leaf; got: {field_stale}"
    );
}

/// A helper's write through a `&mut` argument reaches the caller, and the false
/// direction is refuted rather than proved.
///
/// The write happens one frame down. Only an *indexed* reference argument's store
/// used to cross back, so a field or scalar write through a `&mut` died with the
/// callee's frame: the caller read its own seed, and the false entries here were
/// *proved* against bodies that return 5. Both directions are toothed.
#[test]
fn a_helpers_write_through_a_mutable_reference_reaches_the_caller() {
    let Some(report) = verify_realistic(&[
        "helper_field_write_reaches_the_caller",
        "a_stale_caller_field_cannot_prove_this",
        "helper_scalar_write_reaches_the_caller",
        "a_stale_caller_scalar_cannot_prove_this",
    ]) else {
        return;
    };
    for name in
        ["helper_field_write_reaches_the_caller", "helper_scalar_write_reaches_the_caller"]
    {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "the helper's write must reach the caller; got: {o}");
    }
    for name in ["a_stale_caller_field_cannot_prove_this", "a_stale_caller_scalar_cannot_prove_this"]
    {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "a stale caller value must not prove this false contract; got: {o}"
        );
    }
}

/// An array element reached through a struct field is one word for the contract and
/// the body, and the write does not spill onto a sibling array's element.
///
/// `x.a[0] = 9; x.a[0]` lowers to `(_1.0)[_2] = 9` and `_0 = copy (_1.0)[_4]`. The
/// element store used to be keyed by the local and index alone, so the write landed
/// under a key the read never consulted and the read returned the *seed* -- the false
/// direction, where `ret == 5` was proved against a body returning 9. The pair below
/// toothes both directions, and the sibling entry catches a store that collides
/// `x.a[0]` with `x.b[0]`.
#[test]
fn a_field_array_element_is_one_word_for_contract_and_body() {
    let Some(report) = verify_realistic(&[
        "a_field_array_write_is_read_back",
        "a_field_array_write_is_not_the_seed",
        "a_sibling_field_array_is_untouched",
    ]) else {
        return;
    };
    let read_back = outcome(&report, "a_field_array_write_is_read_back");
    assert!(
        read_back.is_verified(),
        "a write to `x.a[0]` must be seen by the read of `x.a[0]`; got: {read_back}"
    );
    let seed = outcome(&report, "a_field_array_write_is_not_the_seed");
    assert!(
        matches!(seed, FnOutcome::Failed { .. }),
        "the pre-write seed must not prove a contract the body refutes; got: {seed}"
    );
    let sibling = outcome(&report, "a_sibling_field_array_is_untouched");
    assert!(
        sibling.is_verified(),
        "writing `x.a[0]` must leave `x.b[0]` alone; got: {sibling}"
    );
}

/// A *nested* array field is the same word on both sides, and the false direction is
/// refuted rather than proved.
///
/// `o.i.a[0] = 9; o.i.a[0]` lowers to `(_1.0.0)[_2] = 9` and `_0 = copy (_1.0.0)[_4]`. The
/// element's key is the whole field chain, so a store that stopped at the first field
/// (`o.i`) would key the write and the read differently and leave the read at the seed --
/// the false direction, where `ret == 5` was proved against a body returning 9.
#[test]
fn a_nested_field_array_element_is_one_word_for_contract_and_body() {
    let Some(report) = verify_realistic(&[
        "a_nested_field_array_write_is_read_back",
        "a_nested_field_array_write_is_not_the_seed",
    ]) else {
        return;
    };
    let read_back = outcome(&report, "a_nested_field_array_write_is_read_back");
    assert!(
        read_back.is_verified(),
        "a nested `o.i.a[0]` write must be seen by the read; got: {read_back}"
    );
    let seed = outcome(&report, "a_nested_field_array_write_is_not_the_seed");
    assert!(
        matches!(seed, FnOutcome::Failed { .. }),
        "the nested pre-write seed must not prove a refuted contract; got: {seed}"
    );
}

/// A helper's write to a field-array element crosses back through a `&mut`, and the read
/// crosses *in* through a `&`; both directions are pinned, with their false twins.
///
/// The callee's write lands in its own element store, so the caller's store has to be
/// re-based on return -- for a whole-local target (`set_first_element(&mut x)`) unchanged,
/// and for a sub-place target (`set_holder_first_element(&mut o.i)`) prefixed with the
/// target's chain. Without either the write died with the frame, the caller read its seed,
/// and the false `ret == 5` was **proved** against a body returning 9. The read direction is
/// the same re-basing run the other way: `read_holder_first_element(&o.i)` reads the
/// caller's `o.i.a[0]`, so its contract decides rather than being unreadable.
#[test]
fn a_field_array_element_crosses_a_reference_argument() {
    let Some(report) = verify_realistic(&[
        "a_helper_field_array_write_is_read_back",
        "a_helper_field_array_write_is_not_the_seed",
        "a_helper_nested_aggregate_element_write_is_read_back",
        "a_helper_nested_aggregate_element_write_is_not_the_seed",
        "a_helper_nested_aggregate_element_read",
    ]) else {
        return;
    };
    for name in [
        "a_helper_field_array_write_is_read_back",
        "a_helper_nested_aggregate_element_write_is_read_back",
        "a_helper_nested_aggregate_element_read",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must decide and verify; got: {o}");
    }
    for name in [
        "a_helper_field_array_write_is_not_the_seed",
        "a_helper_nested_aggregate_element_write_is_not_the_seed",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "`{name}` claims the caller's seed after the helper wrote; must be refuted, got: {o}"
        );
    }
}

/// An array handed over *as* a reference target (`&mut x.a`) used to be `Incomplete` in
/// both directions. It now *decides*: the true contract is `Verified` and the false twin is
/// refuted -- and the pair is what makes the decision trustworthy.
///
/// The callee's `(*_1)[0] = 9` lands in its own element store, and the return path re-bases
/// it onto the caller's field-path store (`elems_path`, keyed by the target's *field* chain
/// `x.a`) instead of dropping it. So the caller's `x.a[0]` read is the callee's write, and
/// `ensures: ret == 9` is provable while `ensures: ret == 5` is refuted.
///
/// This test is the tripwire the *hole* was pinned with, kept in its stronger form. While
/// the shape was unmodelled it asserted `Incomplete`; the fix that made it decide is the
/// change the pin existed to police, because a re-basing that connected the two stores the
/// *wrong* way would turn the false twin `Verified` first. It did not: the twin is `Failed`.
/// If a later change makes this shape incomplete again, this test fails and the two
/// assertions say exactly which direction broke.
#[test]
fn a_whole_array_target_decides_without_a_false_proof() {
    let Some(report) = verify_realistic(&[
        "a_whole_array_target_crosses_a_reference_argument",
        "a_whole_array_target_cannot_prove_this",
        "a_whole_array_target_sibling_cannot_prove_this",
        "a_whole_array_target_read_crosses_a_reference_argument",
        "a_whole_array_target_read_cannot_prove_this",
        "a_whole_array_target_read_modify_write",
        "a_whole_array_target_read_modify_write_cannot_prove_this",
        "a_nested_whole_array_target_crosses_a_reference_argument",
        "a_nested_whole_array_target_cannot_prove_this",
        "a_whole_array_target_crosses_two_frames",
        "a_whole_array_target_crosses_two_frames_cannot_prove_this",
    ]) else {
        return;
    };
    let o = outcome(&report, "a_whole_array_target_crosses_a_reference_argument");
    assert!(
        o.is_verified(),
        "a `&mut x.a` array target re-bases the callee's element onto the caller's \
         field-path store, so the true contract `ret == 9` must verify; got: {o}"
    );
    let twin = outcome(&report, "a_whole_array_target_cannot_prove_this");
    assert!(
        matches!(twin, FnOutcome::Failed { .. }),
        "the false twin of the whole-array target must be refuted -- a false proof is the \
         only unacceptable outcome, and `Verified` here would be one; got: {twin}"
    );
    let sibling = outcome(&report, "a_whole_array_target_sibling_cannot_prove_this");
    assert!(
        !sibling.is_verified(),
        "the write to `x.a` must not leak into the sibling `x.b`, so claiming `x.b[0]` \
         changed must not verify; got: {sibling}"
    );
    let read = outcome(&report, "a_whole_array_target_read_crosses_a_reference_argument");
    assert!(
        read.is_verified(),
        "the read-only direction (`peek_of(&x.a)`) must also decide -- the carry-in \
         re-bases the caller's field-path element onto the callee's store, so `ret == 5` \
         verifies; got: {read}"
    );
    let read_twin = outcome(&report, "a_whole_array_target_read_cannot_prove_this");
    assert!(
        !read_twin.is_verified(),
        "the false read-only twin (`ret == 7` against a seed of 5) must not verify; \
         got: {read_twin}"
    );
    // The three shapes below are the re-basing rule applied where it is easy to get it
    // *partly* right: a read-modify-write (both directions in one call), a target two
    // fields deep, and a write that crosses two frames. Each true contract must decide
    // and each false twin must be refuted -- a fix that handled only the write, or only
    // a single-field chain, or only one frame, would show up as a true direction stuck
    // `Incomplete` (or, worse, a twin `Verified`).
    for (name, want) in [
        ("a_whole_array_target_read_modify_write", true),
        ("a_whole_array_target_read_modify_write_cannot_prove_this", false),
        ("a_nested_whole_array_target_crosses_a_reference_argument", true),
        ("a_nested_whole_array_target_cannot_prove_this", false),
        ("a_whole_array_target_crosses_two_frames", true),
        ("a_whole_array_target_crosses_two_frames_cannot_prove_this", false),
    ] {
        let got = outcome(&report, name);
        if want {
            assert!(got.is_verified(), "`{name}` must verify; got: {got}");
        } else {
            assert!(
                !got.is_verified(),
                "`{name}` is a false direction and must not verify; got: {got}"
            );
        }
    }
}

/// A method's returned reference to an *element* re-bases onto the caller's element.
///
/// `x.first_mut()` is `&mut x.a[0]`, and the dump names the element index with a
/// local (`_2`), not the literal. Translating the returned reference to the caller
/// therefore has to resolve that local *before* the callee's frame is gone; carrying
/// it through left a place no element store is keyed by, the write `*x.first_mut() = 9`
/// was dropped, and the contract was unreadable -- `Incomplete` in both directions.
/// The true contract must now decide and the false twin must be refuted; the sibling
/// element is the second tooth, because a fix that pinned every returned element to
/// index 0 would decide the first case and read the wrong element here.
#[test]
fn a_returned_reference_to_an_element_reaches_the_caller() {
    let Some(report) = verify_realistic(&[
        "returned_ref_to_an_element_crosses_the_frame",
        "returned_ref_to_an_element_cannot_prove_this",
        "returned_ref_to_a_sibling_element",
        "returned_ref_to_a_sibling_element_cannot_prove_this",
        "returned_ref_write_is_not_the_wrong_element_cannot_prove_this",
        "returned_ref_to_a_whole_array_element",
        "returned_ref_to_a_whole_array_element_cannot_prove_this",
        "returned_ref_to_a_nested_whole_array_element",
        "returned_ref_to_a_nested_whole_array_element_cannot_prove_this",
        "returned_ref_to_a_guarded_symbolic_element",
        "returned_ref_to_a_guarded_symbolic_element_cannot_prove_this",
        "returned_ref_to_an_unpinned_symbolic_element_cannot_prove_this",
        "a_shifted_symbolic_element_cannot_prove_this",
        "a_shifted_symbolic_element_is_not_proved",
    ]) else {
        return;
    };
    for name in [
        "returned_ref_to_an_element_crosses_the_frame",
        "returned_ref_to_a_sibling_element",
        "returned_ref_to_a_whole_array_element",
        "returned_ref_to_a_nested_whole_array_element",
        "returned_ref_to_a_guarded_symbolic_element",
    ] {
        let o = outcome(&report, name);
        assert!(
            o.is_verified(),
            "the write through the returned element reference must reach the caller's \
             element, so `{name}` must verify; got: {o}"
        );
    }
    for name in [
        "returned_ref_to_an_element_cannot_prove_this",
        "returned_ref_to_a_sibling_element_cannot_prove_this",
        "returned_ref_write_is_not_the_wrong_element_cannot_prove_this",
        "returned_ref_to_a_whole_array_element_cannot_prove_this",
        "returned_ref_to_a_nested_whole_array_element_cannot_prove_this",
        "returned_ref_to_a_guarded_symbolic_element_cannot_prove_this",
        "returned_ref_to_an_unpinned_symbolic_element_cannot_prove_this",
    ] {
        let o = outcome(&report, name);
        assert!(
            !o.is_verified(),
            "`{name}` is a false direction -- a write aimed at the wrong element would \
             prove it; got: {o}"
        );
    }
    // The shifted-numbering pair is a *refusal* in both directions: the write may
    // land on any element, so neither `ret == 9` nor `ret == 5` decides. The false
    // direction must not be proved (the write must not be aimed at a caller local
    // that shares the callee index's number), and the true direction must not be
    // proved either (dropping the write must not leave the seed readable).
    for name in [
        "a_shifted_symbolic_element_cannot_prove_this",
        "a_shifted_symbolic_element_is_not_proved",
    ] {
        let o = outcome(&report, name);
        assert!(
            !o.is_verified(),
            "`{name}` must be a refusal -- a symbolic returned index names no single \
             element, so neither direction decides; got: {o}"
        );
    }
}

/// A helper's write-back covers a *nested* field and a read-modify-write, and the
/// caller's field seed crosses *into* the callee so the callee's read is modelled.
///
/// Two teeth here. The nested false entry must be refuted rather than proved: the
/// helper sets `o.i.v = 9` and the caller returns it, so `ret == 0` is false, and
/// a write-back that missed the nested chain would leave the caller's seed and
/// prove it. The read-modify-write entry must *verify* rather than go incomplete:
/// the callee reads `c.lo` before writing it, so carrying only the write-back
/// leaves the callee's read unmodelled and the contract unproved.
#[test]
fn a_helpers_nested_and_read_modify_write_through_a_reference_are_modelled() {
    let Some(report) = verify_realistic(&[
        "helper_nested_write_reaches_the_caller",
        "a_stale_caller_nested_cannot_prove_this",
        "read_modify_write_through_helper",
    ]) else {
        return;
    };
    let nested = outcome(&report, "helper_nested_write_reaches_the_caller");
    assert!(nested.is_verified(), "a nested write through a `&mut` must reach the caller; got: {nested}");
    let stale = outcome(&report, "a_stale_caller_nested_cannot_prove_this");
    assert!(
        matches!(stale, FnOutcome::Failed { .. }),
        "a stale caller nested value must not prove this false contract; got: {stale}"
    );
    let rmw = outcome(&report, "read_modify_write_through_helper");
    assert!(rmw.is_verified(), "a read-modify-write through a `&mut` must be modelled; got: {rmw}");
}

/// The write-back keys the *target's projection*, so `&mut c.lo` lands on the
/// field and a conditional helper write follows the callee's branch.
///
/// A target with a projection (`&mut c.lo`) must not be written to the caller's
/// local: that puts a bit-vector where a struct lives and leaves `c.lo` at its
/// seed, which is how the false twin here was *proved*. A conditional helper write
/// has to reach the caller from the branch it takes, so the `c == true` case reads
/// 5 -- and the false twin, whose precondition pins both the seed and the flag,
/// must be refuted rather than proved.
#[test]
fn a_helper_write_lands_on_the_targets_projection() {
    let Some(report) = verify_realistic(&[
        "helper_write_reaches_a_field_target",
        "a_stale_field_target_cannot_prove_this",
        "helper_write_reaches_a_nested_target",
        "a_stale_nested_target_cannot_prove_this",
        "conditional_helper_write_reaches_the_caller",
        "a_conditional_helper_write_cannot_prove_this",
    ]) else {
        return;
    };
    for name in [
        "helper_write_reaches_a_field_target",
        "helper_write_reaches_a_nested_target",
        "conditional_helper_write_reaches_the_caller",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "a helper write must reach the caller; got: {o}");
    }
    for name in [
        "a_stale_field_target_cannot_prove_this",
        "a_stale_nested_target_cannot_prove_this",
        "a_conditional_helper_write_cannot_prove_this",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "a stale caller value must not prove this false contract; got: {o}"
        );
    }
}

/// A reference to an array *element* (`set5(&mut a[0])`) is a sub-place target too,
/// and a by-value argument's callee write must stay in the callee.
///
/// Two opposite directions in one test. The element target has to land the write at
/// `a[0]` and leave `a[1]` readable: the callee holds the caller's array under its
/// own local, its whole-place write poisons that store, and copying the store back
/// unconditionally would make the *untouched* sibling unknown -- which is why the
/// copy-back is gated on a whole-local target. The by-value pair is the other
/// direction: `set_five_by_value(x)` writes its own copy, so the caller must still
/// read its seed, and a leak back would prove the false `ret == 5`.
#[test]
fn an_element_target_is_written_and_a_by_value_copy_is_not() {
    let Some(report) = verify_realistic(&[
        "helper_write_reaches_an_element_target",
        "a_stale_element_target_cannot_prove_this",
        "an_element_write_leaves_its_sibling",
        "a_stale_element_sibling_cannot_prove_this",
        "a_by_value_callee_write_stays_in_the_callee",
        "a_by_value_callee_write_cannot_prove_this",
    ]) else {
        return;
    };
    for name in [
        "helper_write_reaches_an_element_target",
        "an_element_write_leaves_its_sibling",
        "a_by_value_callee_write_stays_in_the_callee",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "this contract must verify; got: {o}");
    }
    for name in [
        "a_stale_element_target_cannot_prove_this",
        "a_stale_element_sibling_cannot_prove_this",
        "a_by_value_callee_write_cannot_prove_this",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "a stale caller value must not prove this false contract; got: {o}"
        );
    }
}

/// A method is inlined by its *last* path component plus its receiver's type,
/// because rustc defines an inherent method as `<impl at file:line:col>::set_lo`
/// but calls it as `Config::set_lo`; a shared tail is disambiguated by the type
/// rather than guessed at.
///
/// Before the tail match, a call to any method was "unmodelled function", so a
/// method's write through `&mut self` was invisible to its caller. The tripwire
/// pins the other direction: `twist` is both a method and a free function here, so
/// the tail alone names two bodies. The call `w.twist(5)` names the receiver's
/// type, so it resolves to `Widget::twist`; inlining the free function instead
/// would write through the wrong shape and *prove* a false contract, so the
/// resolution must pick the method and refute the claim.
#[test]
fn a_method_is_inlined_by_its_tail_and_a_shared_tail_resolves_by_type() {
    let Some(report) = verify_realistic(&[
        "a_method_write_reaches_the_caller",
        "a_method_write_cannot_prove_this",
        "a_method_read_modify_write",
        "a_method_leaves_its_sibling",
        "a_stale_sibling_cannot_prove_this",
        "an_ambiguous_method_tail_cannot_prove_this",
        "a_generic_method",
        "an_associated_fn_and_builder_chain",
        "a_trait_method",
        "a_tuple_struct_read_method",
        "a_method_with_an_argument",
        "a_reborrow_target_reaches_the_caller",
        "a_stale_reborrow_cannot_prove_this",
        "a_tuple_component_target_reaches_the_caller",
        "a_stale_tuple_component_cannot_prove_this",
    ]) else {
        return;
    };
    for name in [
        "a_method_write_reaches_the_caller",
        "a_method_read_modify_write",
        "a_method_leaves_its_sibling",
        // The shapes a method can take: a generic receiver, an associated function
        // feeding a `&mut self` builder that returns `&mut Self`, a trait method,
        // and a `&self` read (on a tuple struct, and with an argument).
        "a_generic_method",
        "an_associated_fn_and_builder_chain",
        "a_trait_method",
        "a_tuple_struct_read_method",
        "a_method_with_an_argument",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "a method write must reach its caller; got: {o}");
    }
    for name in ["a_method_write_cannot_prove_this", "a_stale_sibling_cannot_prove_this"] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "a stale caller value must not prove this false contract; got: {o}"
        );
    }
    // A reborrow (`&mut *r`) and a tuple component (`&mut t.0`) are sub-place targets
    // too, and both land on the caller's storage.
    for name in [
        "a_reborrow_target_reaches_the_caller",
        "a_tuple_component_target_reaches_the_caller",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "a sub-place target must reach the caller; got: {o}");
    }
    for name in [
        "a_stale_reborrow_cannot_prove_this",
        "a_stale_tuple_component_cannot_prove_this",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "a stale caller value must not prove this false contract; got: {o}"
        );
    }
    // The tail `twist` is shared by `Widget::twist` and a free `twist`, but the
    // call `w.twist(5)` names its receiver's type, so the resolver picks the
    // method by that type rather than by the tail alone. Answering it from the
    // free function -- which writes through a `&mut u8` -- would *prove* this
    // false contract; the correct body sets `w.v = 5`, so the postcondition is
    // refuted. Refuted is the evidence the right body was chosen.
    let o = outcome(&report, "an_ambiguous_method_tail_cannot_prove_this");
    assert!(
        matches!(o, FnOutcome::Failed { .. }),
        "a shared method tail must resolve to the receiver's own body and refute \
         the false contract, not prove it; got: {o}"
    );
}

/// A helper that *reads* its referent, a read-modify-write helper, a two-reference
/// call, and a nested *aggregate* target.
///
/// Each of these needs something the write-only case did not. A read needs the
/// referent's value carried *into* the callee (`_1` otherwise holds the reference
/// temp's `Unknown`, so `*v` is an unmodelled operand). A sub-place aggregate target
/// (`&mut o.i`) needs both the carry-in and the write-back re-based on the target's
/// projection -- dropping the write there refuted the true `ret == 5` and *proved*
/// the false `ret == 0`, which is why the false twin is pinned.
#[test]
fn a_reference_argument_is_read_and_written_through_its_target() {
    let Some(report) = verify_realistic(&[
        "a_read_through_a_helper",
        "a_stale_read_through_a_helper_cannot_prove_this",
        "a_bump_through_a_helper",
        "a_stale_bump_cannot_prove_this",
        "two_reference_arguments",
        "two_reference_arguments_other",
        "two_reference_arguments_swapped_cannot_prove_this",
        "a_swap_through_two_references",
        "a_swap_through_two_references_other",
        "a_stale_swap_cannot_prove_this",
        "a_nested_aggregate_target_reaches",
        "a_stale_nested_aggregate_cannot_prove_this",
        "a_nested_aggregate_read",
        "a_stale_nested_aggregate_read_cannot_prove_this",
    ]) else {
        return;
    };
    for name in [
        "a_read_through_a_helper",
        "a_bump_through_a_helper",
        "two_reference_arguments",
        "two_reference_arguments_other",
        "a_swap_through_two_references",
        "a_swap_through_two_references_other",
        "a_nested_aggregate_target_reaches",
        "a_nested_aggregate_read",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "a reference argument must reach its target; got: {o}");
    }
    for name in [
        "a_stale_read_through_a_helper_cannot_prove_this",
        "a_stale_bump_cannot_prove_this",
        "two_reference_arguments_swapped_cannot_prove_this",
        "a_stale_swap_cannot_prove_this",
        "a_stale_nested_aggregate_cannot_prove_this",
        "a_stale_nested_aggregate_read_cannot_prove_this",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "a stale or unread referent must not prove this false contract; got: {o}"
        );
    }
}

/// The receiver *shapes* a method arrives in: a nested-field receiver, two calls in
/// sequence, a reborrowed receiver, a `&self` read feeding a `&mut` write, and a leaf
/// write that must leave its sibling at the caller's seed.
///
/// These decide through the same inlining and write-back as the plain receiver, which
/// is the point: the receiver is just another argument, and its target is a sub-place
/// (`o.i`) rather than a whole local.
#[test]
fn a_method_receiver_is_a_sub_place_like_any_other_argument() {
    let Some(report) = verify_realistic(&[
        "a_method_on_a_nested_receiver",
        "a_stale_nested_receiver_cannot_prove_this",
        "two_methods_in_sequence",
        "a_stale_first_method_cannot_prove_this",
        "a_method_through_a_reborrow",
        "a_stale_reborrow_receiver_cannot_prove_this",
        "a_read_method_feeds_a_write",
        "a_stale_read_method_cannot_prove_this",
        "a_leaf_write_leaves_its_sibling",
        "a_stale_leaf_sibling_cannot_prove_this",
    ]) else {
        return;
    };
    for name in [
        "a_method_on_a_nested_receiver",
        "two_methods_in_sequence",
        "a_method_through_a_reborrow",
        "a_read_method_feeds_a_write",
        "a_leaf_write_leaves_its_sibling",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "a method receiver must reach its target; got: {o}");
    }
    for name in [
        "a_stale_nested_receiver_cannot_prove_this",
        "a_stale_first_method_cannot_prove_this",
        "a_stale_reborrow_receiver_cannot_prove_this",
        "a_stale_read_method_cannot_prove_this",
        "a_stale_leaf_sibling_cannot_prove_this",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "a stale receiver value must not prove this false contract; got: {o}"
        );
    }
}

/// A helper that forwards its reference to another helper, and a helper that
/// *returns* the reference it was given.
///
/// The returned reference is the sharp case: `let r = identity(&mut x); *r = 5`
/// lowers to `_3 = &mut _1; _2 = identity(_3); (*_2) = 5`, so the write is keyed on
/// a local the *call* defined. Without the reference's origin crossing the call,
/// `_2` had no address, the write went to a local no caller reads, and the false
/// `ret == 0` was proved while the true `ret == 5` was refuted.
#[test]
fn a_reference_crosses_a_call_in_both_directions() {
    let Some(report) = verify_realistic(&[
        "a_two_frame_chain",
        "a_stale_two_frame_chain_cannot_prove_this",
        "a_two_frame_constant",
        "a_stale_two_frame_constant_cannot_prove_this",
        "a_write_through_a_returned_reference",
        "a_stale_returned_reference_cannot_prove_this",
    ]) else {
        return;
    };
    for name in [
        "a_two_frame_chain",
        "a_two_frame_constant",
        "a_write_through_a_returned_reference",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "a forwarded reference must reach its target; got: {o}");
    }
    for name in [
        "a_stale_two_frame_chain_cannot_prove_this",
        "a_stale_two_frame_constant_cannot_prove_this",
        "a_stale_returned_reference_cannot_prove_this",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "a dropped write must not prove this false contract; got: {o}"
        );
    }
}

/// A method that *returns* a reference to one of its own fields.
///
/// `*c.lo_mut() = 5` lowers to `_2 = Config::lo_mut(move _3); (*_2) = 5; _0 = c.lo`,
/// and inside the callee the returned reference is `&mut (*_1).0` -- a place in the
/// *callee's* terms. Translating its head through the argument's caller place gives
/// `c.lo`. Without that the returned reference named nothing, the write was dropped,
/// the true `ret == 5` was refuted, and the false `ret == 0` was **proved**.
#[test]
fn a_method_may_return_a_reference_to_its_own_field() {
    let Some(report) = verify_realistic(&[
        "a_write_through_a_returned_field_reference",
        "a_stale_returned_field_reference_cannot_prove_this",
        "a_write_through_the_other_returned_reference",
        "a_stale_other_returned_reference_cannot_prove_this",
        "a_write_through_a_returned_builder",
        "a_stale_returned_builder_cannot_prove_this",
    ]) else {
        return;
    };
    for name in [
        "a_write_through_a_returned_field_reference",
        "a_write_through_the_other_returned_reference",
        "a_write_through_a_returned_builder",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "a returned field reference must reach the field; got: {o}");
    }
    for name in [
        "a_stale_returned_field_reference_cannot_prove_this",
        "a_stale_other_returned_reference_cannot_prove_this",
        "a_stale_returned_builder_cannot_prove_this",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "a dropped write through a returned reference must not prove this; got: {o}"
        );
    }
}

/// A returned reference may name a *nested* place, or a place in a *different*
/// argument.
///
/// The nested case (`&mut o.i.v`) needs the whole projection carried, not just the
/// head local, and the two-argument case needs the translation to pick the argument
/// the reference was actually built from rather than the first one.
#[test]
fn a_returned_reference_carries_its_whole_projection() {
    let Some(report) = verify_realistic(&[
        "a_write_through_a_returned_nested_reference",
        "a_stale_returned_nested_reference_cannot_prove_this",
        "a_returned_nested_reference_leaves_its_sibling",
        "a_write_through_a_method_nested_reference",
        "a_stale_method_nested_reference_cannot_prove_this",
        "a_write_through_a_second_argument_reference",
        "a_stale_second_argument_reference_cannot_prove_this",
    ]) else {
        return;
    };
    for name in [
        "a_write_through_a_returned_nested_reference",
        "a_returned_nested_reference_leaves_its_sibling",
        "a_write_through_a_method_nested_reference",
        "a_write_through_a_second_argument_reference",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "a returned reference must reach its place; got: {o}");
    }
    for name in [
        "a_stale_returned_nested_reference_cannot_prove_this",
        "a_stale_method_nested_reference_cannot_prove_this",
        "a_stale_second_argument_reference_cannot_prove_this",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "a dropped write through a returned reference must not prove this; got: {o}"
        );
    }
}

/// A returned reference fed straight into another call, reborrowed, held alongside a
/// second returned reference to a different field, or naming a tuple component.
///
/// The reborrow (`let s = &mut *r` where `r` came from a call) and the pass-through
/// (`write_one(identity(&mut c.lo))`) both go through the same `addressed` mapping
/// the returned reference installs. Two returned references to different fields must
/// not collapse onto one, and a tuple component is a returned place the write-back key
/// *can* spell (`Field(0)`), unlike an array element.
#[test]
fn a_returned_reference_composes_with_the_next_use() {
    let Some(report) = verify_realistic(&[
        "a_reference_returned_into_another_call",
        "a_stale_returned_into_another_call_cannot_prove_this",
        "a_reborrow_of_a_returned_reference",
        "a_stale_reborrow_of_a_returned_reference_cannot_prove_this",
        "two_returned_field_references",
        "a_stale_two_returned_fields_cannot_prove_this",
        "a_returned_tuple_component_reference",
        "a_stale_tuple_component_reference_cannot_prove_this",
    ]) else {
        return;
    };
    for name in [
        "a_reference_returned_into_another_call",
        "a_reborrow_of_a_returned_reference",
        "two_returned_field_references",
        "a_returned_tuple_component_reference",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "a returned reference must compose with its next use; got: {o}");
    }
    for name in [
        "a_stale_returned_into_another_call_cannot_prove_this",
        "a_stale_reborrow_of_a_returned_reference_cannot_prove_this",
        "a_stale_two_returned_fields_cannot_prove_this",
        "a_stale_tuple_component_reference_cannot_prove_this",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "a dropped or misplaced write must not prove this false contract; got: {o}"
        );
    }
}

/// Two `&mut` targets in one call: two *aggregate* fields, or two *elements* of one
/// array.
///
/// The two writes must stay independent -- the false twins read the *other* target,
/// and would verify if the two targets collapsed onto one place. The swap shapes read
/// both referents, so they also exercise the carry-in.
#[test]
fn two_reference_targets_in_one_call_stay_independent() {
    let Some(report) = verify_realistic(&[
        "two_aggregate_reference_targets",
        "two_aggregate_reference_targets_other",
        "a_stale_two_aggregate_targets_cannot_prove_this",
        "a_swap_of_two_aggregate_targets",
        "a_stale_swap_of_aggregate_targets_cannot_prove_this",
        "two_elements_through_one_reference",
        "two_elements_through_one_reference_other",
        "a_stale_two_elements_cannot_prove_this",
        "a_swap_of_two_elements",
        "a_stale_swap_of_elements_cannot_prove_this",
    ]) else {
        return;
    };
    for name in [
        "two_aggregate_reference_targets",
        "two_aggregate_reference_targets_other",
        "a_swap_of_two_aggregate_targets",
        "two_elements_through_one_reference",
        "two_elements_through_one_reference_other",
        "a_swap_of_two_elements",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "two reference targets must stay independent; got: {o}");
    }
    for name in [
        "a_stale_two_aggregate_targets_cannot_prove_this",
        "a_stale_swap_of_aggregate_targets_cannot_prove_this",
        "a_stale_two_elements_cannot_prove_this",
        "a_stale_swap_of_elements_cannot_prove_this",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "collapsed or stale targets must not prove this false contract; got: {o}"
        );
    }
}

/// A *scalar* field reached through a `&T`/`&mut T` argument, both read and written.
///
/// The referent's parts are carried into the callee, so the callee's `d.v` resolves to
/// the caller's `d.v`; the write-back then re-bases on the target's projection, which
/// is empty here (the target is the whole local). An enum *payload* through a reference
/// stays sound-incomplete -- the discriminant switch is unmodelled -- which is the
/// honest refusal rather than a dropped write.
#[test]
fn a_scalar_field_crosses_a_reference_argument() {
    let Some(report) = verify_realistic(&[
        "a_scalar_field_read_through_a_reference",
        "a_stale_scalar_field_read_cannot_prove_this",
        "a_scalar_field_write_through_a_reference",
        "a_stale_scalar_field_write_cannot_prove_this",
    ]) else {
        return;
    };
    for name in [
        "a_scalar_field_read_through_a_reference",
        "a_scalar_field_write_through_a_reference",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "a scalar field must cross a reference argument; got: {o}");
    }
    for name in [
        "a_stale_scalar_field_read_cannot_prove_this",
        "a_stale_scalar_field_write_cannot_prove_this",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "a stale scalar field must not prove this false contract; got: {o}"
        );
    }
}

/// A reference reached *through* another reference, and a reference to a local copy.
///
/// `**rr = 5` lowers to `_4 = no_retag copy (*_3); (*_4) = 5` with `_4: &mut u8`. The
/// `no_retag` prefix left the rvalue unparsed and the deref-of-a-reference copy had no
/// address, so the write was dropped: the *false* `ret == 0` proved and the true
/// `ret == 5` refuted. The read shape `**rr` had the same hole, and a write through a
/// reference to a local *copy* must not reach the original.
#[test]
fn a_reference_through_a_reference_is_not_dropped() {
    let Some(report) = verify_realistic(&[
        "a_write_through_two_levels_of_reference",
        "a_stale_two_level_write_cannot_prove_this",
        "a_read_through_two_levels_of_reference",
        "a_stale_two_level_read_cannot_prove_this",
        "a_write_to_a_copy_stays_in_the_copy",
        "a_stale_copy_write_cannot_prove_this",
    ]) else {
        return;
    };
    for name in [
        "a_write_through_two_levels_of_reference",
        "a_read_through_two_levels_of_reference",
        "a_write_to_a_copy_stays_in_the_copy",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "a two-level reference must reach its place; got: {o}");
    }
    for name in [
        "a_stale_two_level_write_cannot_prove_this",
        "a_stale_two_level_read_cannot_prove_this",
        "a_stale_copy_write_cannot_prove_this",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "a dropped two-level write, or an aliasing copy, must not prove this; got: {o}"
        );
    }
}

/// A copy between two reference targets, a field through a *double* reference, and a
/// call through a reference to a reference.
///
/// `*r = *s` on two `&mut` to different fields must copy the right way, and
/// `(**rr).lo = 5` resolves both levels inside the frame. The *argument* case
/// (`relay(&mut r)` with `v: &mut &mut u8`) crosses two frames and is refused rather
/// than modelled -- the callee's write had been dropped, proving a false `ret == 0`.
#[test]
fn a_reference_to_a_reference_crosses_a_frame_only_when_refused() {
    let Some(report) = verify_realistic(&[
        "a_copy_between_two_reference_targets",
        "a_stale_copy_between_reference_targets_cannot_prove_this",
        "a_write_through_a_double_reference_to_a_struct",
        "a_stale_double_reference_struct_cannot_prove_this",
        "a_call_through_a_reference_to_a_reference_is_refused",
    ]) else {
        return;
    };
    for name in [
        "a_copy_between_two_reference_targets",
        "a_write_through_a_double_reference_to_a_struct",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "a local reference chain must be modelled; got: {o}");
    }
    for name in [
        "a_stale_copy_between_reference_targets_cannot_prove_this",
        "a_stale_double_reference_struct_cannot_prove_this",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "a stale or misdirected reference write must not prove this; got: {o}"
        );
    }
    let refused = outcome(&report, "a_call_through_a_reference_to_a_reference_is_refused");
    assert!(
        matches!(refused, FnOutcome::Incomplete { .. }),
        "a `&mut &mut T` call must be refused, not decided; got: {refused}"
    );
}

/// An array that is a struct *field* carries its elements when the aggregate is moved.
///
/// `ArrayHolder { a: [9, 1, 2, 3] }` builds the array in a temp whose elements live in the
/// whole-local `elems` store, then moves it into the field. `rebase_parts` re-based
/// `elems_path` (field-path arrays) but missed `elems`, so `x.a[0]` read `Unknown` and the
/// contract stayed `Incomplete` in *both* directions -- a coverage hole, not a false proof,
/// since a missing value proves nothing. A bare array literal always worked, so the hole
/// was specific to the field case. The whole-field write through a reference (`*h = n`)
/// exercises the same carry across a frame, and the sibling check keeps the re-base from
/// spilling the elements onto a neighbouring scalar.
#[test]
fn an_array_field_of_a_moved_aggregate_carries_its_elements() {
    let Some(report) = verify_realistic(&[
        "a_struct_literal_array_element_is_read_back",
        "a_struct_literal_array_element_is_not_the_seed_cannot_prove_this",
        "a_struct_literal_array_second_element_is_read_back",
        "a_struct_literal_array_second_element_is_not_the_first_cannot_prove_this",
        "a_nested_struct_literal_array_element_is_read_back",
        "a_nested_struct_literal_array_element_is_not_the_seed_cannot_prove_this",
        "a_whole_field_assignment_carries_its_array_elements",
        "a_stale_whole_field_array_element_cannot_prove_this",
        "a_whole_field_assignment_leaves_its_sibling",
        "a_whole_field_assignment_leaves_its_sibling_cannot_prove_this",
        "an_array_field_argument_is_read_by_element",
        "an_array_field_argument_is_read_by_element_cannot_prove_this",
    ]) else {
        return;
    };
    for name in [
        "a_struct_literal_array_element_is_read_back",
        "a_struct_literal_array_second_element_is_read_back",
        "a_nested_struct_literal_array_element_is_read_back",
        "a_whole_field_assignment_carries_its_array_elements",
        "a_whole_field_assignment_leaves_its_sibling",
        "an_array_field_argument_is_read_by_element",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "an array field's elements must reach the read; got: {o}");
    }
    for name in [
        "a_struct_literal_array_element_is_not_the_seed_cannot_prove_this",
        "a_struct_literal_array_second_element_is_not_the_first_cannot_prove_this",
        "a_nested_struct_literal_array_element_is_not_the_seed_cannot_prove_this",
        "a_stale_whole_field_array_element_cannot_prove_this",
        "a_whole_field_assignment_leaves_its_sibling_cannot_prove_this",
        "an_array_field_argument_is_read_by_element_cannot_prove_this",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "a stale or misdirected array-field element must not prove this; got: {o}"
        );
    }
}

/// A whole-aggregate replacement through a sub-place target decides.
///
/// `set_whole(&mut o.i, InnerBox { v: 9 })` replaces the whole referent. This was once
/// believed *sound-incomplete* -- a leaf write "cannot spell a whole value" -- but the
/// re-based write-back re-roots the callee's `fields` entry for the moved value under the
/// target's chain, and in this store a whole value and a leaf are both a `fields` entry, so
/// the shape was never actually the blocker. The sibling check keeps the re-root from
/// landing on the whole local, and the local-built value makes the carry come from a temp.
#[test]
fn a_whole_aggregate_replacement_through_a_sub_place_decides() {
    let Some(report) = verify_realistic(&[
        "whole_replacement_through_sub_place",
        "whole_replacement_through_sub_place_cannot_prove_this",
        "whole_replacement_leaves_the_sibling",
        "whole_replacement_leaves_the_sibling_cannot_prove_this",
        "whole_replacement_from_a_local",
        "whole_replacement_from_a_local_cannot_prove_this",
    ]) else {
        return;
    };
    for name in [
        "whole_replacement_through_sub_place",
        "whole_replacement_leaves_the_sibling",
        "whole_replacement_from_a_local",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "a whole replacement must reach the caller's leaf; got: {o}");
    }
    for name in [
        "whole_replacement_through_sub_place_cannot_prove_this",
        "whole_replacement_leaves_the_sibling_cannot_prove_this",
        "whole_replacement_from_a_local_cannot_prove_this",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "a stale or misdirected whole replacement must not prove this; got: {o}"
        );
    }
}

/// A named `const` item's value is inlined at the use site.
///
/// rustc const-evaluates a `const` item and prints its *body* separately
/// (`const LIMIT: u8 = const 10_u8;`) while referring to it by name at the use
/// site (`_0 = const LIMIT`). Reading only the name left the use site an
/// unreadable path constant, so a contract that mentioned the constant was lost.
/// The true directions must decide, and each false twin -- whose postcondition is
/// false on *every* input -- must be refuted, which is what a regression that
/// guessed the value would fail.
#[test]
fn a_named_const_item_is_inlined_at_its_use_site() {
    let Some(report) = verify_realistic(&[
        "named_const_is_read",
        "named_const_is_read_cannot_prove_this",
        "named_const_keeps_its_width",
        "named_const_keeps_its_width_cannot_prove_this",
        "named_bool_const_selects",
        "named_bool_const_selects_cannot_prove_this",
        "named_const_bounds_a_comparison",
        "named_const_bounds_a_comparison_cannot_prove_this",
        "named_const_matches_an_equality",
        "named_const_matches_an_equality_cannot_prove_this",
        "named_negative_const_is_signed",
        "named_negative_const_is_signed_cannot_prove_this",
        "nested_module_const_is_read",
        "nested_module_const_is_read_cannot_prove_this",
    ]) else {
        return;
    };
    for name in [
        "named_const_is_read",
        "named_const_keeps_its_width",
        "named_bool_const_selects",
        "named_const_bounds_a_comparison",
        "named_const_matches_an_equality",
        "named_negative_const_is_signed",
        "nested_module_const_is_read",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "a named const must fold at its use site; got: {o}");
    }
    for name in [
        "named_const_is_read_cannot_prove_this",
        "named_const_keeps_its_width_cannot_prove_this",
        "named_bool_const_selects_cannot_prove_this",
        "named_const_bounds_a_comparison_cannot_prove_this",
        "named_const_matches_an_equality_cannot_prove_this",
        "named_negative_const_is_signed_cannot_prove_this",
        "nested_module_const_is_read_cannot_prove_this",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "a wrong inlined const value must not prove this; got: {o}"
        );
    }
}

/// A contract may name a top-level `const` the way the body does.
///
/// The reader resolves a bare name against the arguments first, then against the
/// program's own `const` table -- the *same* table the executor folds a body's
/// `const LIMIT` from, so the two cannot disagree. The true directions must decide,
/// and each false twin must be refuted; a name that resolved to nothing (or to a
/// wrong value) would leave the twin unproved or, worse, prove it.
///
/// The two cases that are *refusals* rather than proofs are checked separately: an
/// expression-bodied constant has no literal to fold, and a misspelled name is not
/// an argument. Both must be `Skipped`, never `verified` and never a wrong value.
#[test]
fn a_contract_may_name_a_const_item() {
    let Some(report) = verify_realistic(&[
        "a_contract_names_a_const",
        "a_contract_names_a_const_cannot_prove_this",
        "a_contract_names_a_negative_const",
        "a_contract_names_a_bool_const",
        "a_contract_names_a_qualified_const",
        "a_contract_names_a_qualified_const_cannot_prove_this",
        "a_contract_names_an_expression_const",
        "a_misspelled_const_is_refused",
    ]) else {
        return;
    };
    for name in [
        "a_contract_names_a_const",
        "a_contract_names_a_negative_const",
        "a_contract_names_a_bool_const",
        "a_contract_names_a_qualified_const",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "a contract must resolve a named const; got: {o}");
    }
    for name in [
        "a_contract_names_a_const_cannot_prove_this",
        "a_contract_names_a_qualified_const_cannot_prove_this",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "a wrong const value must not prove this; got: {o}"
        );
    }
    for name in ["a_contract_names_an_expression_const", "a_misspelled_const_is_refused"] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Skipped { .. }),
            "an unresolvable const name must be refused, not guessed; got: {o}"
        );
    }
}

/// A function-local `const` is not in scope in another function.
///
/// `a_local_const_owner` declares `const L: u8 = 3;` in its body; the dump prints
/// that definition bare (`const L: u8 = const 3_u8;`) -- the same spelling a
/// crate-level `const` gets -- while its *use* is qualified (`const
/// a_local_const_owner::L`). A bare program-wide key for the definition let the
/// other function's `requires: L == 3` resolve to a name its own source could not
/// write, so the function was *proved* from a foreign body: a wrong proof, not a
/// lost one. The name must resolve to nothing here, leaving the function `Skipped`
/// (unreadable `requires`), never `Verified`.
///
/// The crate-level constant path stays covered by
/// [`a_contract_may_name_a_const_item`], so this pins that the scope rule did not
/// also drop the in-scope names.
#[test]
fn a_local_const_is_not_in_scope_in_another_function() {
    let Some(report) = verify_realistic(&[
        "a_local_const_owner",
        "a_local_const_is_not_in_scope_in_another_function",
    ]) else {
        return;
    };
    let owner = outcome(&report, "a_local_const_owner");
    assert!(owner.is_verified(), "the owner reads its own local const; got: {owner}");
    let other = outcome(&report, "a_local_const_is_not_in_scope_in_another_function");
    assert!(
        !other.is_verified(),
        "a contract must not resolve another function's local const -- that is a \
         wrong proof; got: {other}"
    );
}

/// The whole-corpus direction invariant: a function whose *name* says it must not be
/// provable may never come back `verified`.
///
/// The corpus pairs each contract with its false twin, spelled `..._cannot_prove_this`:
/// the same body, or one differing only in the direction of the claim, so a twin that
/// verifies is a false proof by construction. Checking the naming convention
/// over the whole file means a new false proof of any *known* shape fails this test the
/// moment it is introduced, instead of waiting for someone to remember to assert the
/// twin in the same commit that adds the shape. It is the corpus-wide version of the
/// per-shape `Failed` assertions below, and it is deliberately weaker than they are --
/// a twin may be `Failed`, `Incomplete` or `Skipped` and this passes, because all three
/// are honest answers and only `verified` is a lie.
#[test]
fn no_cannot_prove_entry_is_ever_verified() {
    let Some(report) = verify_realistic(&[]) else { return };
    let mut checked = 0usize;
    let mut liars = Vec::new();
    for (name, o) in &report.outcomes {
        // The suffix is the whole convention: all 49 probes in the corpus use it, and
        // none uses a prefix. A name that does not end this way is not a
        // false-direction probe, whatever else it looks like.
        let false_direction = name.ends_with("_cannot_prove_this");
        if !false_direction {
            continue;
        }
        checked += 1;
        if o.is_verified() {
            liars.push(name.clone());
        }
    }
    assert!(
        liars.is_empty(),
        "these entries claim a false contract and were `verified` -- a false proof: {liars:?}"
    );
    // A silent zero would make this test vacuous if the naming convention ever drifts,
    // so the count is asserted rather than merely reported.
    assert!(
        checked >= 40,
        "expected the corpus to carry dozens of false-direction probes, found {checked}; \
         has the naming convention changed?"
    );
}
/// A deep term is refused, not allowed to overflow the stack.
///
/// The engine's contract is that a query it cannot decide is *reported*: `Unknown`,
/// `Incomplete`, a budget trip -- never a crash. Every budget before this one counted
/// *steps*, and steps are not what a stack overflow is made of: `udiv(x, 3)` at 64 bits
/// builds a chain of adders and muxes ~262 terms deep, which is a few hundred steps, so it
/// passed every step budget and then aborted the process. On a 2 MiB stack -- the default
/// for a Rust test thread -- the walk wanted ~600 KiB in release and more in debug.
///
/// The guard is `MAX_WALK_DEPTH`, and this test is what holds it: it runs on the test
/// thread's own stack, so a regression that removes the guard aborts the test binary
/// (SIGABRT) instead of failing an assertion. The division-by-a-non-power-of-two shape is
/// the deepest legitimate walk in the corpus; the assertion that it reports rather than
/// panics is the whole point.
///
/// The deep walk needs a *symbolic* dividend: a precondition that pins the dividend folds
/// the whole divider to a literal (see [`a_signed_division_by_a_non_power_of_two_at_i64`]),
/// so the pinned shape no longer builds the deep term at all. The companion
/// [`a_symbolic_division_by_a_non_power_of_two_at_i64`] keeps the dividend free and is the
/// vehicle here.
#[test]
fn a_deep_term_walk_is_refused_not_allowed_to_overflow_the_stack() {
    let Some(report) = verify_realistic(&[
        "a_symbolic_division_by_a_non_power_of_two_at_i64",
        "a_signed_division_by_a_non_power_of_two_at_i64",
        "a_signed_constant_division_at_i64",
    ]) else {
        return;
    };
    // The symbolic case is the one that used to crash. Either answer but `Verified` is
    // acceptable -- the general divider is a documented scaling wall -- and the
    // unacceptable one is a false proof. Reaching this assertion at all is the fix.
    let deep = outcome(&report, "a_symbolic_division_by_a_non_power_of_two_at_i64");
    assert!(
        !deep.is_verified(),
        "the general divider must not be reported verified: {deep}"
    );
    // The *pinned* shape is now decided: the precondition leaves one dividend, the fold
    // collapses the divider to a literal, and the false contract is refuted. This is the
    // positive evidence that the fold, not a tighter budget, is what closed it -- a depth
    // bound that refused both shapes would pass the assertion above and be useless.
    let pinned = outcome(&report, "a_signed_division_by_a_non_power_of_two_at_i64");
    assert!(
        pinned.is_verified(),
        "the pinned divider must be decided by the fold, got: {pinned}"
    );
    // The power-of-two fast path is shallow and must still be *decided*, so the depth
    // bound cannot be so tight that it refuses the queries the engine already answers.
    let shallow = outcome(&report, "a_signed_constant_division_at_i64");
    assert!(
        shallow.is_verified(),
        "the power-of-two fast path must still verify: {shallow}"
    );
}

/// A pin applies to an aggregate *part*, not only to a whole argument.
///
/// `requires: w.v == -7` names a struct field, `requires: o.i.v == -7` names a nested
/// path, and `requires: xs[0] == -7` names an array element. All three are the same shape
/// as the argument-level pin -- a closed equality in the precondition, under any nesting of
/// `&&` -- but the variable the contract binds is a part's, not a local's. Keying the pin by
/// the argument's *local* reached none of them, so the body's `w.v / 3` stayed symbolic and
/// built the 64-bit restoring divider: `incomplete` in ~1.2s, decided in ~0s once the pin is
/// keyed by the variable's own index.
///
/// The `cannot_prove_this` companions are the point of the test. Without them, an engine
/// that answered `Verified` for everything would pass the positive assertions, so the
/// negatives are what make "decided" mean "decided correctly": the fold refutes a wrong
/// claim about the same pinned part, which is only possible if the value really is `-7`.
#[test]
fn a_pin_reaches_an_aggregate_part_not_only_a_whole_argument() {
    let Some(report) = verify_realistic(&[
        "a_field_pinned_division_at_i64",
        "a_field_pinned_division_cannot_prove_this",
        "a_nested_pinned_division_at_i64",
        "a_nested_pinned_division_cannot_prove_this",
        "an_element_pinned_division_at_i64",
        "an_element_pinned_division_cannot_prove_this",
    ]) else {
        return;
    };
    for name in [
        "a_field_pinned_division_at_i64",
        "a_nested_pinned_division_at_i64",
        "an_element_pinned_division_at_i64",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "a pinned aggregate part must be decided; `{name}` got: {o}");
    }
    for name in [
        "a_field_pinned_division_cannot_prove_this",
        "a_nested_pinned_division_cannot_prove_this",
        "an_element_pinned_division_cannot_prove_this",
    ] {
        let o = outcome(&report, name);
        assert!(
            !o.is_verified(),
            "a false claim about a pinned part must be refuted, not proved; `{name}` got: {o}"
        );
    }
}

/// A callee's contract is never taken on faith: its body is inlined, so a lying
/// `ensures` cannot be inherited by a caller, and a vacuous `requires` cannot be
/// used to assume a false postcondition.
///
/// This is the soundness property with the largest blast radius -- assuming a
/// callee's postcondition is the canonical way a modular verifier proves a false
/// contract -- so it is pinned directly rather than left implied by the absence of
/// a bug report. The recursion cases are the same property under the inductive
/// hypothesis, where an unguarded assumption is easiest to make.
#[test]
fn a_callee_contract_is_never_assumed() {
    let Some(report) = verify_realistic(&[
        "a_helper_whose_contract_is_false",
        "a_caller_of_a_lying_helper_cannot_prove_this",
        "a_caller_of_a_lying_helper_knows_the_truth",
        "a_call_that_violates_a_precondition_is_not_checked",
        "a_call_that_divides_by_zero_cannot_prove_this",
        "a_vacuous_helper_whose_postcondition_is_false",
        "a_caller_inheriting_a_vacuous_lie_cannot_prove_this",
        "a_caller_of_a_vacuous_helper_knows_the_truth",
        "a_recursive_contract_that_is_false_cannot_prove_this",
        "a_mutual_lie_a_cannot_prove_this",
        "a_mutual_lie_b_cannot_prove_this",
        "an_invariant_false_on_entry_cannot_prove_this",
        "an_invariant_not_preserved_cannot_prove_this",
    ]) else {
        return;
    };

    // The two entries that must verify are the *honest* directions: they are what
    // proves the shapes above are decidable at all, rather than undecided for a
    // reason that happens to look safe.
    for name in [
        "a_caller_of_a_lying_helper_knows_the_truth",
        "a_caller_of_a_vacuous_helper_knows_the_truth",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "the honest direction must verify; `{name}` got: {o}");
    }

    // A callee's `requires` is not an obligation at the call site -- the body is
    // inlined instead -- so this one verifies, and that is the honest answer rather
    // than a false proof: the helper returns its argument whatever it is. Pinning it
    // makes the *choice* visible instead of accidental.
    let unchecked = outcome(&report, "a_call_that_violates_a_precondition_is_not_checked");
    assert!(
        unchecked.is_verified(),
        "a callee precondition is not a call-site obligation; expected verified, got: {unchecked}"
    );

    for name in [
        "a_helper_whose_contract_is_false",
        "a_caller_of_a_lying_helper_cannot_prove_this",
        "a_call_that_divides_by_zero_cannot_prove_this",
        "a_vacuous_helper_whose_postcondition_is_false",
        "a_caller_inheriting_a_vacuous_lie_cannot_prove_this",
        "a_recursive_contract_that_is_false_cannot_prove_this",
        "a_mutual_lie_a_cannot_prove_this",
        "a_mutual_lie_b_cannot_prove_this",
        "an_invariant_false_on_entry_cannot_prove_this",
        "an_invariant_not_preserved_cannot_prove_this",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "an assumed callee contract, an unchecked induction, or a vacuous \
             precondition must not prove this; `{name}` got: {o}"
        );
    }
}

/// A slice's length is read through the *one* rvalue the compiler prints, on any
/// toolchain.
///
/// `PtrMetadata(copy _1)` is what 1.99 and later print for a `&[T]`'s length;
/// before 1.99 (the MSRV, 1.85) the same query prints as `Len((*_1))`. Two things
/// had to hold for the entry to decide on both: `Len` had to be modelled at all,
/// and its argument had to survive parsing. `trim_end_matches(')')` stripped *both*
/// trailing parens, leaving `(*_1` -- unparseable, so the length was `Unknown` and
/// the bounds check above `a[i]` was unmodelled, turning this decidable entry into
/// an incomplete one on 1.85 only. The entry decides identically on both now.
#[test]
fn a_slices_length_is_read_on_any_toolchain() {
    let Some(report) = verify_realistic(&["slice_symbolic_index"]) else { return };
    let o = outcome(&report, "slice_symbolic_index");
    assert!(o.is_verified(), "the slice entry must decide on any toolchain; got: {o}");
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
/// Verify one function from an inline source and return its outcome.
///
/// Each test below needs its own file, because the property under test is about
/// what the *frontend* does with a specific shape and the corpus is shared.
/// Writing the source to a temp dir keeps that shape next to its assertion.
///
/// Returns `None` only when no nightly `rustc` is configured, which is the one
/// legitimate reason to skip. A named function that is *absent* from the report
/// is a panic, not a skip: it means the frontend dropped it, and a test written
/// as `let Some(o) = verify_src(..) else { return }` would then pass without
/// checking anything. That is how `a_whole_struct_assignment_invalidates_its_fields`
/// hid a one-line struct that swallowed every following function. A vacuous pass
/// is worse than a failure, so this refuses to be quiet about it.
///
/// The guard `verify_src` applies: a contracted function that is absent from the
/// report is a failure, whatever `report.missing` says. `missing` is the same
/// drop from the frontend's side (a contract with no MIR function), and accepting
/// it as a pass reopened the hole the guard exists to close: a test whose function
/// the frontend drops -- for *any* reason, including one a future bug adds --
/// would assert nothing. The only source without a contract is one that carries no
/// `///` at all, which is a caller mistake, not a frontend drop.
///
/// Split out so the branch that made the guard vacuous -- `missing` naming the
/// function -- can be tested *without* a nightly `rustc`. The guard is about what
/// counts as a pass, and a test that needed the frontend could not check the one
/// case that mattered.
#[track_caller]
fn assert_not_dropped(name: &str, src: &str, present: bool, missing: &[String]) {
    assert!(
        present || !src.contains("///"),
        "`{name}` was dropped from the report: it has a contract but no outcome, so this test \
         would have passed without checking anything (missing: {missing:?})"
    );
}

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
    assert_not_dropped(name, src, o.is_some(), &report.missing);
    o
}

/// A contracted function the frontend dropped is a failure, even when the report
/// names it in `missing`.
///
/// `missing` is the drop reported from the frontend's side, and accepting it as a
/// pass reopened the hole the strict helper exists to close: a test whose function
/// the frontend drops -- for any reason, including one a future bug adds -- would
/// assert nothing. The guard must reject the `missing` case, which is what this
/// pins without needing a nightly `rustc`.
#[test]
#[should_panic(expected = "was dropped")]
fn a_dropped_contracted_function_fails_even_when_missing_names_it() {
    assert_not_dropped("ghost", "/// ensures: true\npub fn ghost() {}", false, &["ghost".to_string()]);
}

/// The guard is not a blanket refusal: a function present in the report passes,
/// and so does a source with no contract at all (which is a caller mistake, not a
/// frontend drop).
#[test]
fn a_present_function_passes_the_drop_guard() {
    assert_not_dropped("f", "/// ensures: true\npub fn f() {}", true, &[]);
    assert_not_dropped("f", "pub fn f() {}", false, &[]);
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

/// A one-line struct body must not swallow the functions that follow it.
///
/// `struct_head` accepted any line containing `{` and opened a multi-line field
/// cursor, so `pub struct B { pub lo: u8 }` left the cursor open with no closing
/// brace left to read: every following line -- including the `///` contracts and
/// the functions -- was consumed as struct fields. The functions then vanished
/// from the spec table and were silently *not checked at all*, which is worse
/// than a wrong verdict because nothing reports it. The test above used a one-line
/// struct and was therefore passing vacuously.
///
/// The struct path now mirrors the enum path: a body that closes on the head line
/// is read inline, and a cursor is opened only for a body that does not. This
/// pins the function after the struct as still present and still decided.
///
/// The `None` case is a *skip*, not a failure, like every other `rustc`-dependent
/// test in this file: `verify_src` returns `None` when no `DISCHARGE_RUSTC` is
/// named, and there is nothing to assert about a compiler that is not there. This
/// one used to `panic!` on `None`, which made the whole suite fail on a machine
/// with no `DISCHARGE_RUSTC` -- the one test in the file that read "no compiler"
/// as "a bug", so the suite's verdict depended on the environment rather than on
/// the code. It is a skip now, and the reason is worth keeping: the property is
/// real and worth pinning, but a missing toolchain is not evidence against it.
#[test]
fn a_one_line_struct_does_not_swallow_the_functions_after_it() {
    let src = r#"
pub struct B { pub lo: u8 }

/// requires: true
/// ensures: ret == 0
pub fn after_inline_struct(x: u8) -> u8 {
    0
}
"#;
    let Some(o) = verify_src("after_inline_struct", src) else { return };
    assert!(o.is_verified(), "the function must still be read and decided; got: {o}");
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

/// A cast in a contract is a *value*, so a relational postcondition about it is
/// decided rather than refused.
///
/// The equality entries pin that a cast *extends* like Rust (`-1i8 as i16` is
/// `-1`, not `255`), but they only ever meet the cast with `==`. A cast the order
/// operator cannot read would be a silently dropped obligation -- the failure mode
/// the tripwire rule exists to catch -- so this pairs three true relational
/// contracts with two that must be refuted. The pair also separates
/// sign-extension from zero-filling *through the order*: `(y as i16) >= 0` for an
/// `i8` `y` is false exactly when the source's sign is kept, and
/// `(y as i16) <= 127` is true exactly when it is.
///
/// The evidence behind the entries is a differential sweep over every cast of a
/// small type into every wider target, compared against an exhaustive Python
/// model: 2160 cases decided, 0 unsound, 0 discrepancies.
#[test]
fn a_cast_in_a_contract_can_be_ordered() {
    let names = [
        "contract_cast_relational_nonneg",
        "contract_cast_relational_lt_width",
        "contract_cast_relational_signed_bound",
        "contract_cast_relational_signed_nonneg_tripwire",
        "contract_cast_relational_positive_tripwire",
    ];
    let Some(report) = verify_realistic(&names) else { return };
    for name in [
        "contract_cast_relational_nonneg",
        "contract_cast_relational_lt_width",
        "contract_cast_relational_signed_bound",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    for name in [
        "contract_cast_relational_signed_nonneg_tripwire",
        "contract_cast_relational_positive_tripwire",
    ] {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Failed { .. }),
            "`{name}` is false for every negative (resp. zero) input; got: {o}"
        );
    }
}

/// The `.wrapping_*` methods are the method-call spelling of the wrapping
/// operators the contract language already models, and reading them is what lets a
/// contract say what a body that uses them *means*.
///
/// Before this, every `x.wrapping_add(y)` in a contract was "cannot read contract",
/// which leaves the function silently outside the check set -- the outcome the
/// frontend exists to avoid. A two-variable relational sweep (208 pairs of
/// `requires`/`ensures` over `u8` `x`, `y`, exhaustive ground truth over all 2^16
/// pairs) went from **120 decided / 88 skipped** to **208 decided / 0 skipped**,
/// with 0 unsound and 0 discrepancies, so the desugaring agrees with Rust on every
/// pair it now reads.
///
/// The two refusals are the teeth: `x.wrapping_add(300)` is a rustc error for its
/// `300` (the wrapping semantics excuse the overflow of the *result*, not an
/// out-of-range literal), and `1.wrapping_add(2)` is `E0689` (an ambiguous
/// `{integer}` receiver). Both must be refused, never given a verdict.
#[test]
fn a_wrapping_method_in_a_contract_is_read_as_the_operator_it_denotes() {
    let names = [
        "contract_wrapping_add_reads",
        "contract_wrapping_add_is_a_value_tripwire",
        "contract_wrapping_sub_mul_chain_reads",
        "contract_wrapping_agrees_with_the_plain_operators",
        "contract_wrapping_neg_on_unsigned_reads",
        "contract_wrapping_neg_on_signed_reads",
        "contract_wrapping_add_of_constants_wraps",
    ];
    let Some(report) = verify_realistic(&names) else { return };
    for name in [
        "contract_wrapping_add_reads",
        "contract_wrapping_sub_mul_chain_reads",
        "contract_wrapping_agrees_with_the_plain_operators",
        "contract_wrapping_neg_on_unsigned_reads",
        "contract_wrapping_neg_on_signed_reads",
        "contract_wrapping_add_of_constants_wraps",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must verify, got: {o}");
    }
    let o = outcome(&report, "contract_wrapping_add_is_a_value_tripwire");
    assert!(
        matches!(o, FnOutcome::Failed { .. }),
        "the wrapping add is a value, so `+ 1` on it is false for every input; got: {o}"
    );

    for name in [
        "contract_wrapping_add_of_an_out_of_range_literal_is_refused",
        "contract_wrapping_add_on_an_untyped_receiver_is_refused",
    ] {
        let Some(report) = verify_realistic(&[name]) else { return };
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Skipped { .. }),
            "`{name}` is a rustc error and must be refused, never given a verdict, got: {o}"
        );
    }
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
        "contract_hex_arithmetic_is_folded",
        "contract_hex_shift_amount",
        "contract_hex_mask_keeps_low_nibble",
        "contract_negative_hex_literal",
        "contract_uppercase_hex_prefix",
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

/// A literal that does not fit the operand's signed width is refused, and the
/// false proof it used to allow is the point.
///
/// `128` for an `i8` is the bit pattern `0x80`, which is `-128` signed. A reader
/// that asked only whether the literal fits in eight *unsigned* bits accepted it, so
/// `x <= 128` was read as `x <= -128` and `ensures: ret <= 127` was *proved* for a
/// body returning `x`. rustc rejects `x <= 128` for an `i8` ("literal out of range
/// for `i8`"), so the correct outcome is a refusal. The `i8::MIN` boundary shares
/// the bit pattern and must still read, which is what keeps the fix from refusing
/// every `0x80`.
#[test]
fn an_out_of_range_literal_is_refused_not_wrapped() {
    let refused = [
        "contract_out_of_range_literal_is_refused",
        "contract_out_of_range_negation_is_refused",
        "contract_constant_vs_constant_out_of_range",
        "contract_constant_sum_overflow_is_refused",
        "contract_constant_underflow_is_refused",
        "contract_constant_div_overflow_is_refused",
        "contract_constant_signed_sum_overflow_is_refused",
        "contract_signed_literal_vs_unsigned_is_refused",
        "contract_signed_constant_sum_vs_unsigned_is_refused",
        "contract_signed_constant_mask_vs_unsigned_is_refused",
        // A negation of a constant is checked against the value it denotes, so a
        // negation that overflows its own type is refused (`-(i8::MIN)`, and the
        // wrapping shift `-(3 << 7)` that shares its bit pattern).
        "contract_negation_of_min_is_refused",
        "contract_negation_of_wrapping_shift_is_refused",
        // A shift *amount* is a value of its own `i32`, so an amount that wraps at
        // the operand's width but not at `i32` (`2 << 7` is `256`) is refused. A
        // nested suffix is in the inner shift's amount, so it does not fix the
        // outer amount's type (`2 << 7u8` is still the `i32` `256`), and a cast
        // fixes the type and overrides what it casts (`(1u8) as u16` is a `u16`,
        // so the amount is `257u16`).
        "contract_nested_shift_amount_overflow_is_refused",
        "contract_nested_shift_amount_sum_overflow_is_refused",
        "contract_nested_amount_suffix_does_not_fix_the_outer_width",
        "contract_cast_amount_operand_fixes_the_width",
    ];
    let Some(report) = verify_realistic(&refused) else { return };
    for name in refused {
        let o = outcome(&report, name);
        assert!(
            !o.is_verified(),
            "`{name}` must be refused, not verified -- verifying it is the false proof, got: {o}"
        );
        assert!(
            matches!(o, FnOutcome::Skipped { .. }),
            "`{name}` must be skipped (unreadable contract), got: {o}"
        );
    }
    let read = [
        "contract_min_bound_still_reads",
        "contract_negative_bound_reads_at_i16",
        "contract_constant_vs_constant_in_range",
        "contract_constant_sum_in_range_reads",
        "contract_constant_sum_wider_operand_reads",
        "contract_unsigned_literal_still_reads",
        "contract_unsigned_constant_sum_still_reads",
        "contract_unsigned_mask_still_reads",
        // The controls for the two classes above: an in-range negation and an
        // amount that fits `i32` both still read, so the refusals are pinned to
        // the overflow and not to the shape. A *typed* amount operand fixes the
        // amount's width, so `1u8 + (2 << 7)` is a `u8` amount (`2 << 7` is `0u8`)
        // and the shift rustc accepts must read rather than be refused.
        "contract_negation_of_max_still_reads",
        "contract_fitting_shift_amount_still_reads",
        "contract_typed_amount_operand_fixes_the_width",
    ];
    let Some(report) = verify_realistic(&read) else { return };
    for name in read {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "`{name}` must still read and verify, got: {o}");
    }
}

/// A signed element of a slice or array must be read as signed *in the contract*.
///
/// `bind_indexed_elem` (and the symbolic-index chain) recorded an element's
/// signedness for the executor's seeds but not for the parser's name table, so
/// `is_signed_name` reported an `i8` element as unsigned. A postcondition that
/// compares it with zero then reads as an unsigned comparison, which is *always
/// true* -- so `ensures: xs[0] >= 0` was reported verified for a body that returns
/// the element, a false proof with `i8::MIN` as the counterexample.
///
/// The existing `signed_slice_element_tripwire` did not catch this: its body reads
/// the element itself, so the *body's* (correct, executor-side) reading dominated
/// the verdict and it was already FAILED for the right reason. The bug only shows
/// when the element appears on the contract side alone, which is what these two
/// entries pin. Both are sensitive: removing either sign record makes them verify.
#[test]
fn a_signed_element_is_read_as_signed_in_the_contract() {
    let refuted = [
        "signed_slice_element_ensures_tripwire",
        "signed_array_chain_ensures_tripwire",
    ];
    let Some(report) = verify_realistic(&refuted) else { return };
    for name in refuted {
        let o = outcome(&report, name);
        let FnOutcome::Failed { kind, detail, .. } = o else {
            panic!(
                "`{name}` is false at `i8::MIN` and must be refuted -- verifying it is \
                 the unsigned-reading false proof, got: {o}"
            );
        };
        assert_eq!(kind, "postcondition", "`{name}` got: {o}");
        // The witness is `128`, the bit pattern of `i8::MIN`. Under the unsigned
        // reading the comparison is trivially true and there is no witness at all.
        assert!(
            detail.contains("= 128"),
            "the witness should be `128` (`i8::MIN`), got: {detail}"
        );
    }
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


/// A contract above a struct or enum belongs to that item, not the next function.
///
/// The reader matched a `struct`/`enum` head and `continue`d without clearing the
/// pending contract, so a doc comment above a layout carried over to the next `fn`.
/// A leaked `requires` is a false proof when it is satisfiable: `requires: x == 0`
/// above a struct made `ensures: ret == 0` for a body returning `x` *verify*,
/// because the check is only made for the inputs the precondition admits.
///
/// Both entries below carry the identical function and contract; the first has a
/// struct above it with a `requires: x == 0`, the second does not. Both must be
/// refuted, and refuted the *same way*. The pair is the evidence: verifying the
/// tripwire would be the false proof, and refuting only the control would not show
/// the leak was dropped.
#[test]
fn a_contract_above_a_layout_does_not_leak_into_the_next_function() {
    let names = ["leaked_requires_tripwire", "leaked_requires_is_dropped"];
    let Some(report) = verify_realistic(&names) else { return };
    for name in names {
        let o = outcome(&report, name);
        let FnOutcome::Failed { kind, .. } = o else {
            panic!("`{name}` proves a false contract; got: {o}");
        };
        assert_eq!(kind, "postcondition", "`{name}` must fail on its postcondition, got: {o}");
    }
}

/// Two names of different signedness are refused, and the same-signedness pair
/// still reads.
///
/// `a > b` for an `i8` and a `u8` is `E0308: mismatched types` in rustc. The
/// reader used to pick a sign and decide it; the body reads each operand at its
/// own signedness, so the contract and the body could disagree about the operator's
/// meaning. Refusing keeps the answer "the tool could not run" rather than a verdict
/// on a program that does not compile. The control is the same comparison with both
/// operands `i8`: it is legal and must still verify, so the refusal is not a blanket
/// ban on two-name comparisons.
#[test]
fn a_mixed_signedness_comparison_is_refused_and_the_same_signedness_pair_reads() {
    let refused = [
        "contract_mixed_signedness_compare_is_refused",
        "contract_mixed_signedness_add_is_refused",
    ];
    let Some(report) = verify_realistic(&refused) else { return };
    for name in refused {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Skipped { .. }),
            "`{name}` must be refused (skipped), not given a verdict, got: {o}"
        );
    }
    let Some(report) = verify_realistic(&["contract_same_signedness_compare_still_reads"]) else {
        return;
    };
    let o = outcome(&report, "contract_same_signedness_compare_still_reads");
    assert!(o.is_verified(), "the same-signedness control must still verify, got: {o}");
}

/// An untyped constant's complement is refused in an *equality*, not just an
/// ordering.
///
/// `!0` has no type of its own. Rust types an untyped constant as `i32`, so `!0`
/// is `-1` and `!0 == 255` is `false`: the postcondition holds for no input. The
/// reader carried the complement as a bit pattern at the scope's width, built
/// `255u8 == 255`, and *verified* it -- a false proof. `==`/`!=` "compare bit
/// patterns" was the reason given for leaving them readable, but here the two
/// readings are different *values* (`-1` vs `255`), so the shape is refused. The
/// control fixes the reading with a typed operand and must still verify.
#[test]
fn an_untyped_complement_equality_is_refused_and_a_typed_partner_reads() {
    let Some(report) = verify_realistic(&["contract_untyped_complement_equality_is_refused"]) else {
        return;
    };
    let o = outcome(&report, "contract_untyped_complement_equality_is_refused");
    assert!(
        matches!(o, FnOutcome::Skipped { .. }),
        "`!0 == 255` is `false` in Rust; it must be refused, never given a verdict, got: {o}"
    );
    let Some(report) =
        verify_realistic(&["contract_complement_of_literal_with_typed_partner_reads"])
    else {
        return;
    };
    let o = outcome(&report, "contract_complement_of_literal_with_typed_partner_reads");
    assert!(o.is_verified(), "a typed partner fixes the reading and must verify, got: {o}");
}

/// The complement of an *out-of-range* literal is refused, while a fitting one
/// still reads and a wider operand is untouched.
///
/// `!128` for an `i8` is a rustc `literal out of range for i8` error -- `128` does
/// not fit a signed eight-bit type -- even though the complement's *value* `127`
/// does. The reader built `!128` as the constant `127` and let the resize truncate
/// it with no check, so `y <= !128` read as `y <= 127` (`i8::MAX`) and *verified*
/// for a program rustc rejects. Two controls keep the refusal at the range: `!127`
/// fits an `i8`, and `!128` fits an `i16`, so both must be *decided* (each is a
/// real predicate, not a tautology, so the verdict is `Failed` with a witness) --
/// a blanket ban on `!`-of-`128` would leave them `Skipped`.
#[test]
fn a_complement_of_an_out_of_range_literal_is_refused() {
    let Some(report) = verify_realistic(&[
        "contract_complement_of_out_of_range_literal_is_refused",
        "contract_fitting_complement_still_reads",
        "contract_complement_reads_at_a_wider_operand",
    ]) else {
        return;
    };
    let o = outcome(&report, "contract_complement_of_out_of_range_literal_is_refused");
    assert!(
        matches!(o, FnOutcome::Skipped { .. }),
        "`y <= !128` for an `i8` is a rustc range error; it must be refused, never given a \
         verdict, got: {o}"
    );
    for name in [
        "contract_fitting_complement_still_reads",
        "contract_complement_reads_at_a_wider_operand",
    ] {
        let o = outcome(&report, name);
        assert!(
            !matches!(o, FnOutcome::Skipped { .. }),
            "{name} fits the operand type and must be decided, got: {o}"
        );
    }
}

/// Unary `-` on an *unsigned* name is refused, and a *signed* negation still reads.
///
/// `-x` for a `u8` is `E0600: cannot apply unary operator `-` to type `u8``. The
/// reader modelled it as `0 - x`, a value Rust never produces, so the shape is
/// refused rather than decided -- the same answer as a mixed-signedness pair. The
/// control negates a signed name, which is legal, and must still verify.
#[test]
fn an_unsigned_negation_is_refused_and_a_signed_negation_reads() {
    let Some(report) = verify_realistic(&["contract_unsigned_negation_is_refused"]) else { return };
    let o = outcome(&report, "contract_unsigned_negation_is_refused");
    assert!(
        matches!(o, FnOutcome::Skipped { .. }),
        "`-x` for a `u8` does not compile and must be refused, got: {o}"
    );
    let Some(report) = verify_realistic(&["contract_signed_negation_still_reads"]) else { return };
    let o = outcome(&report, "contract_signed_negation_still_reads");
    assert!(o.is_verified(), "a negation of a signed name must still verify, got: {o}");
}

/// A contract literal widened to meet a *signed* operand zero-fills.
///
/// The fill comes from the constant's own signedness, not the operand it meets.
/// Rust's `(255u8 as i16)` is `255`, so `(x as i16) == 255` holds for every `u8`
/// `x`. Widening the literal from the operand's signed `i16` sign-extended it to
/// `65535` and *refuted* a postcondition Rust accepts -- a false refutation. The
/// control `254` is neither reading and must FAIL, so the fix is not "verify
/// everything".
#[test]
fn a_literal_widened_to_a_signed_operand_zero_fills() {
    let Some(report) = verify_realistic(&["contract_literal_widened_to_signed_zero_fills"]) else {
        return;
    };
    let o = outcome(&report, "contract_literal_widened_to_signed_zero_fills");
    assert!(o.is_verified(), "`255` widened to i16 is `255` and must verify, got: {o}");
    let Some(report) = verify_realistic(&["contract_literal_widened_to_signed_tripwire"]) else {
        return;
    };
    let o = outcome(&report, "contract_literal_widened_to_signed_tripwire");
    assert!(matches!(o, FnOutcome::Failed { .. }), "`254` is neither reading and must FAIL, got: {o}");
}

/// Every literal and every constant `+ - *` intermediate is range-checked against
/// the type the expression meets, not only the value the fold produces.
///
/// The reader folds a constant expression to one value and used to range-check
/// only that value. Rust checks each literal and each intermediate: `2 & 128` for
/// an `i8` is a `literal out of range` error although the fold's value is `0`, and
/// `128 - 63` is rejected although its value `65` fits. The reader decided both --
/// a wrong verdict on a program rustc rejects, where the previous fix's class was
/// a false *proof*. Two controls keep the refusal at the range: the same literals
/// under a `u8` partner fit, and `-128` is rescued by the unary `-` because the
/// negated value, not the magnitude, is what meets the type.
#[test]
fn a_literal_inside_a_constant_fold_is_range_checked_too() {
    let refused = [
        "contract_literal_in_fold_out_of_range_is_refused",
        "contract_masked_literal_out_of_range_is_refused",
        "contract_constant_sum_value_out_of_range_is_refused",
        "contract_literal_in_difference_out_of_range_is_refused",
        "contract_literal_in_negated_fold_is_refused",
        "contract_complement_shift_amount_is_refused",
    ];
    let Some(report) = verify_realistic(&refused) else { return };
    for name in refused {
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Skipped { .. }),
            "`{name}` is a rustc range error and must be refused, never given a verdict, got: {o}"
        );
    }
    for name in [
        "contract_fold_literals_in_range_still_read",
        "contract_bare_negated_bound_still_reads",
    ] {
        let Some(report) = verify_realistic(&[name]) else { return };
        let o = outcome(&report, name);
        assert!(o.is_verified(), "{name} fits the type it meets and must verify, got: {o}");
    }
}

/// A constant fold that mixes an *untyped* complement with a plain operand is
/// refused when its value depends on the signedness Rust infers for it.
///
/// A complement has no signedness of its own: it takes the one the type it meets
/// gives it. The reader guesses it from the other operand, and when no operand
/// fixes a sign the guess can disagree with the reading the fold finally gets.
/// `!127 - 63` is `128 - 63 = 65` unsigned but `i8::MIN - 63` -- a rustc overflow --
/// signed, so the reader decided `65` for a program rustc rejects: a wrong verdict.
/// `!127 * 2` is the same shape. A negated bare literal beside a complement
/// (`!100 * -0`) is `E0277` for a `u16` -- legal only at a signed type -- so it is
/// refused too. Two controls keep the refusal at the ambiguity: the same fold under
/// a wider partner is in range under both readings and reads, and a fold that
/// agrees under both readings (`(!0) - 1`) still reads.
#[test]
fn a_sign_ambiguous_untyped_fold_is_refused() {
    for name in [
        "contract_sign_ambiguous_fold_is_refused",
        "contract_sign_ambiguous_mul_is_refused",
        "contract_complement_with_negated_literal_is_refused",
    ] {
        let Some(report) = verify_realistic(&[name]) else { return };
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Skipped { .. }),
            "`{name}` is sign-ambiguous and must be refused, never given a verdict, got: {o}"
        );
    }
    for name in [
        "contract_sign_ambiguous_fold_at_wider_width_reads",
        "contract_agreeing_untyped_fold_still_reads",
    ] {
        let Some(report) = verify_realistic(&[name]) else { return };
        let o = outcome(&report, name);
        assert!(o.is_verified(), "{name} agrees under both readings and must verify, got: {o}");
    }
}

/// A complement's *provisional* unsigned value must not be range-checked as if it
/// were a written literal, while a literal *under* the fold still is.
///
/// `y == !(!1 + 1)` for an `i8` `y` is valid Rust: `!1 + 1` is `-1` at `i8` and
/// `!(-1)` is `0`, so the contract is `y == 0`. The reader evaluates the fold
/// unsigned (`255`) because its type is not known until it meets the `i8`, and
/// range-checking that guess refused the contract although no `255` is written. The
/// fold now records only its operands' envelopes, so the guess is not checked -- the
/// control shows a genuine literal under the fold (`!128`) is still range-checked
/// against the type the complement meets and is refused.
#[test]
fn an_opaque_folds_provisional_value_is_not_range_checked() {
    let Some(report) =
        verify_realistic(&["contract_opaque_fold_provisional_value_is_not_range_checked"])
    else {
        return;
    };
    let o = outcome(&report, "contract_opaque_fold_provisional_value_is_not_range_checked");
    assert!(o.is_verified(), "`y == !(!1 + 1)` is `y == 0` and must verify, got: {o}");
    let Some(report) =
        verify_realistic(&["contract_literal_under_complement_is_still_range_checked"])
    else {
        return;
    };
    let o = outcome(&report, "contract_literal_under_complement_is_still_range_checked");
    assert!(
        matches!(o, FnOutcome::Skipped { .. }),
        "`!128` is an `i8` range error and must be refused, got: {o}"
    );
}

/// The written magnitude of a suffixed literal is what Rust range-checks, and a
/// complement's operand envelope must not leak onto an unrelated literal that
/// shares the complement's value term.
///
/// `128i8` alone is a `literal out of range for i8` error and only `-128i8` is
/// legal, because the negation is what meets the type. Recording the *signed value*
/// (`-128`) instead of the written magnitude made the negation add `+128` to the
/// envelope and refuse the valid `-128i8`; it also made the positive `128i8`, which
/// rustc rejects, read as the in-range `-128` -- a wrong verdict in both directions.
/// The complement is worse: at eight bits `!128` is the constant `127`, which the
/// engine hash-conses with a separately written bare `127`, so recording the
/// operand envelope (`128`) on that shared id skipped the valid
/// `x == !128 && y == 127`. The envelope now travels in the operand's own payload.
///
/// Two follow-ups. A *nested* complement whose operand is a fold must union the
/// envelope it inherited with the one the fold recorded on its own term, or the
/// fold's out-of-range literal is dropped and the reader decides a contract rustc
/// rejects (`y == !(!1 - 200)` for an `i8`). And a *named bound* (`i8::MIN`) shares
/// its bit pattern with a bare or suffixed `128`, so the term-keyed envelope map
/// charged the literal's `128` to the bound and skipped a valid contract; the bound
/// is now built as a term of its own.
#[test]
fn a_suffixed_minimum_and_a_complement_operand_are_checked_where_they_are_written() {
    for name in [
        "contract_suffixed_positive_min_magnitude_is_refused",
        "contract_double_negated_min_is_refused",
        "contract_complement_operand_out_of_range_is_refused",
        "contract_negated_complement_operand_is_refused",
        "contract_nested_complement_fold_operand_is_refused",
    ] {
        let Some(report) = verify_realistic(&[name]) else { return };
        let o = outcome(&report, name);
        assert!(
            matches!(o, FnOutcome::Skipped { .. }),
            "`{name}` is a rustc range error and must be refused, never given a verdict, got: {o}"
        );
    }
    for name in [
        "contract_suffixed_min_literal_still_reads",
        "contract_suffixed_positive_literal_still_reads",
        "contract_complement_does_not_pollute_a_bare_literal",
        "contract_named_min_after_suffixed_min_reads",
        "contract_suffixed_min_after_named_min_reads",
        "contract_named_min_after_bare_128_reads",
    ] {
        let Some(report) = verify_realistic(&[name]) else { return };
        let o = outcome(&report, name);
        assert!(o.is_verified(), "{name} is valid Rust and must verify, got: {o}");
    }
}

/// An *opaque* constant (a complement) widened to a wider operand is refused, and
/// a *fold* is not.
///
/// A complement is taken at the *operand's* width, but the reader holds it at the
/// *scope's*. `!0` against a `u16` is `65535`, so `(x as u16 + !0) == 255` is false
/// in Rust; the reader held `255` and zero-extended it, and *verified* the equality
/// -- a false proof. The signed case fails the same way when the literal's top bit
/// is clear (`!128` against an `i16` is `-129`, not `127`). Both are refused. A
/// *fold* (`200 + 100`) is a value and must still verify.
#[test]
fn an_opaque_widening_is_refused_but_a_fold_widens() {
    let Some(report) = verify_realistic(&[
        "contract_opaque_widened_to_unsigned_is_refused",
        "contract_opaque_widened_to_signed_is_refused",
        "contract_fold_widens_to_unsigned_reads",
    ]) else {
        return;
    };
    for name in [
        "contract_opaque_widened_to_unsigned_is_refused",
        "contract_opaque_widened_to_signed_is_refused",
    ] {
        let o = outcome(&report, name);
        assert!(
            !o.is_verified(),
            "{name} must not verify -- the reader cannot model the complement at the operand width, got: {o}"
        );
    }
    let o = outcome(&report, "contract_fold_widens_to_unsigned_reads");
    assert!(o.is_verified(), "a fold widens exactly and must verify, got: {o}");
}

/// A *suffixed* literal keeps its own width, so a cast of it is not re-read from
/// the names in scope.
///
/// `128i16` is a sixteen-bit `128`, and `128i16 as i32` is `128` in Rust. Sizing
/// the literal from the scope instead -- eight bits here, the only names in scope
/// -- made `128i16` the bit pattern `0x80`, which the widening cast sign-extended
/// to `-128`, and *verified* `ensures: 128i16 as i32 == -128`, a postcondition Rust
/// calls false. The true counterpart (`== 128`) must verify, so the fix is not
/// "refuse every suffixed literal".
#[test]
fn a_suffixed_literal_keeps_its_own_width() {
    let Some(report) = verify_realistic(&[
        "contract_suffixed_literal_keeps_its_width",
        "contract_suffixed_literal_is_its_own_value",
    ]) else {
        return;
    };
    let o = outcome(&report, "contract_suffixed_literal_keeps_its_width");
    assert!(
        !o.is_verified(),
        "`128i16 as i32` is `128`, so `== -128` is false and must not verify, got: {o}"
    );
    let o = outcome(&report, "contract_suffixed_literal_is_its_own_value");
    assert!(o.is_verified(), "`128i16 as i32 == 128` is true and must verify, got: {o}");
}

/// A fold that touches a complement is a width-dependent bit pattern, so its
/// widening is refused; the valid masked and shifted shapes still read.
///
/// `!0 + 2` is `1` in Rust (the complement is `-1`), so
/// `(x as i16 + 2) == !0 + 2` is false; the reader held the complement at the
/// scope's width, added `2` to get `257`, and a later resize truncated it into
/// `i16`'s `1`, *verifying* the false equality. `!0 & 1` is `1` at any width and
/// `!0 >> 0` is `!0`, so both of those must still verify -- the refusal is drawn
/// at the width *depending* on the operand, not at the complement.
#[test]
fn a_complement_fold_widening_is_refused_but_masks_and_shifts_read() {
    let Some(report) = verify_realistic(&[
        "contract_complement_fold_widening_is_refused",
        "contract_complement_mask_widens_exactly",
        "contract_complement_shift_by_zero_reads",
        "contract_complement_division_with_typed_operand_reads",
    ]) else {
        return;
    };
    let o = outcome(&report, "contract_complement_fold_widening_is_refused");
    assert!(!o.is_verified(), "`(x as i16 + 2) == !0 + 2` is false and must not verify, got: {o}");
    for name in [
        "contract_complement_mask_widens_exactly",
        "contract_complement_shift_by_zero_reads",
        "contract_complement_division_with_typed_operand_reads",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "{name} is a valid contract and must verify, got: {o}");
    }
}

/// An untyped fold that *overflows* the operand width is refused, while a fold
/// that fits still reads.
///
/// `!0 + 1` is `256` at the scope's width; against a `u8` that is a rustc
/// `arithmetic operation will overflow` error (`!0` is `255`), but the reader
/// truncated the scope-width fold to the partner's width and read `(!0 + 1) < 1u8`
/// as `0 < 1` -- *verified* for a program rustc rejects. `(!0 + 2) == 1u8` failed
/// the same way (`257` truncated to `1`). Both must be refused. `200 + 100` is
/// `300` at any width holding it, so it is width-independent and must still read.
#[test]
fn an_untyped_fold_overflow_is_refused_but_a_fitting_fold_reads() {
    let Some(report) = verify_realistic(&[
        "contract_untyped_fold_overflow_is_refused",
        "contract_untyped_fold_overflow_equality_is_refused",
        "contract_fitting_fold_still_reads",
    ]) else {
        return;
    };
    for name in [
        "contract_untyped_fold_overflow_is_refused",
        "contract_untyped_fold_overflow_equality_is_refused",
    ] {
        let o = outcome(&report, name);
        assert!(
            !o.is_verified(),
            "{name} folds an untyped constant into a value that overflows the operand width \
             (`E0308`/overflow in Rust) and must be refused, got: {o}"
        );
    }
    let o = outcome(&report, "contract_fitting_fold_still_reads");
    assert!(
        o.is_verified(),
        "`200 + 100` is width-independent and must verify, got: {o}"
    );
}

/// A shift of an *untyped* constant whose width Rust infers is refused when it is
/// only valid at the scope's width, while a shift that is valid at every width
/// reads.
///
/// `255 >> 8` is fine at the scope's width (32, from a `u32` name in scope), but
/// the operand has no type of its own: against a `u8` partner `255` is a `u8`, and
/// a shift by its own width is a rustc `arithmetic operation will overflow`. The
/// reader verified `255 >> 8 <= x` on a program rustc rejects. `(255 >> 1) >= y`
/// for an `i8` `y` failed the same way (`255` is a rustc `literal out of range`).
/// Both must be refused. `1 << 4` is `16` at any width holding it, and a shift of a
/// typed name has a known width, so both must still read.
#[test]
fn an_untyped_shift_that_needs_a_wider_operand_is_refused_but_a_fitting_shift_reads() {
    let Some(report) = verify_realistic(&[
        "contract_untyped_shift_amount_over_narrow_width_is_refused",
        "contract_untyped_left_shift_amount_over_narrow_width_is_refused",
        "contract_untyped_shift_operand_out_of_narrow_range_is_refused",
        "contract_fitting_untyped_shift_still_reads",
        "contract_typed_shift_still_reads",
    ]) else {
        return;
    };
    for name in [
        "contract_untyped_shift_amount_over_narrow_width_is_refused",
        "contract_untyped_left_shift_amount_over_narrow_width_is_refused",
        "contract_untyped_shift_operand_out_of_narrow_range_is_refused",
    ] {
        let o = outcome(&report, name);
        assert!(
            !o.is_verified(),
            "{name} shifts an untyped constant by an amount (or with a value) that is only \
             valid at the scope's width, not the width Rust infers from the partner, and must \
             be refused, got: {o}"
        );
    }
    for name in [
        "contract_fitting_untyped_shift_still_reads",
        "contract_typed_shift_still_reads",
    ] {
        let o = outcome(&report, name);
        assert!(
            o.is_verified(),
            "{name} is a shift whose width is known or whose value fits every width, and must \
             verify, got: {o}"
        );
    }
}

/// A `u128`-suffixed literal is *refused*, not panicked.
///
/// The suffix records width 128, and the range check that guards the literal
/// computes `1u128 << w`. At `w == 128` that shift panics in a debug build (it
/// wraps to a wrong `max` in release, which then lets a 128-bit literal reach
/// `smt::word` -- itself an assertion). The refusal has to come *before* the
/// shift. The two literals here are both small, so the value is not the problem;
/// the *type* is. This pins that the reader reports the function as skipped
/// instead of taking the run down, which is what a panic does.
#[test]
fn a_u128_suffix_literal_is_refused_not_panicked() {
    let src = "/// requires: true\n/// ensures: 0u128 == 0u128\n\
               pub fn f(x: u8) -> u8 { x }";
    let Some(o) = verify_src("f", src) else { return };
    let FnOutcome::Skipped { reason } = o else {
        panic!("a `u128`-suffixed literal must be refused, got: {o}");
    };
    assert!(
        reason.contains("128") && reason.contains("64-bit"),
        "the refusal should name the width and the engine limit, got: {reason}"
    );
}

/// A *symbolic* masked operand keeps its type, so a signed/unsigned pairing is
/// refused rather than given a signed reading.
///
/// `x & 128` for a `u8` is a `u8`; masking does not change its operand's type.
/// Marking the result untyped (`Sign::Literal`) let `refuse_mixed_signedness`
/// accept `(x & 128) == y` for a signed `y` -- a pairing rustc rejects (E0308) --
/// and decide it as a signed comparison. The contract must be refused, and the
/// valid *constant* mask (`(!0 & 1)`, width-independent) must still read.
#[test]
fn a_symbolic_mask_keeps_its_type_but_a_constant_mask_still_widens() {
    let Some(report) = verify_realistic(&[
        "contract_symbolic_mask_keeps_its_type",
        "contract_complement_mask_widens_exactly",
    ]) else {
        return;
    };
    let o = outcome(&report, "contract_symbolic_mask_keeps_its_type");
    assert!(
        !o.is_verified(),
        "`(x & 128) == y` pairs a `u8` with an `i8` and must be refused, got: {o}"
    );
    let o = outcome(&report, "contract_complement_mask_widens_exactly");
    assert!(
        o.is_verified(),
        "a constant width-independent mask still widens and must verify, got: {o}"
    );
}

/// A constant whose *type is fixed* may not meet a partner of another width.
///
/// `-1i8` is an `i8`, so `-1i8 < (x as i16)` is `E0308` even though both operands
/// are signed; `refuse_mixed_signedness` passes them, so the width is the only
/// remaining evidence, and `align_widths` used to resize the constant and erase it
/// — *verifying* the contract. A *bare* negation (`-1`) has no width of its own, so
/// it still meets a wider operand. The mismatch and the valid control are asserted
/// together, because the rule must refuse only a fixed width.
#[test]
fn a_fixed_width_constant_may_not_meet_a_partner_of_another_width() {
    let Some(report) = verify_realistic(&[
        "contract_fixed_width_constant_vs_wider_cast_is_refused",
        "contract_two_fixed_width_constants_are_refused",
        "contract_bare_negation_meets_a_wider_operand",
    ]) else {
        return;
    };
    for name in [
        "contract_fixed_width_constant_vs_wider_cast_is_refused",
        "contract_two_fixed_width_constants_are_refused",
    ] {
        let o = outcome(&report, name);
        assert!(
            !o.is_verified(),
            "{name} compares a fixed-width constant with a differently-sized operand \
             (`E0308`) and must be refused, got: {o}"
        );
    }
    let o = outcome(&report, "contract_bare_negation_meets_a_wider_operand");
    assert!(
        o.is_verified(),
        "a bare negation infers its width and is well-typed, so it must verify, got: {o}"
    );
}

/// A *typed* constant mask keeps its type, so a pairing of the other signedness is
/// refused rather than decided — in **both** directions.
///
/// `-1i8 & 1` is an `i8` and `1u8 & 1` is a `u8`, even though both compute the
/// small positive `1`: the mask takes the typed operand's type and `==` never
/// coerces. Marking the constant result `Literal` hid the type, so a pairing with
/// the *other* signedness -- `E0308` in Rust -- was read as `1 == y` and
/// *verified*. The first fix excluded only a *signed* typed operand, leaving the
/// unsigned half open; both must be refused, and the same mask against a partner of
/// its own signedness must still verify.
#[test]
fn a_typed_constant_mask_keeps_its_type() {
    let Some(report) = verify_realistic(&[
        "contract_signed_mask_vs_unsigned_is_refused",
        "contract_signed_mask_with_signed_partner_reads",
        "contract_unsigned_mask_vs_signed_is_refused",
        "contract_unsigned_mask_with_unsigned_partner_reads",
    ]) else {
        return;
    };
    for name in [
        "contract_signed_mask_vs_unsigned_is_refused",
        "contract_unsigned_mask_vs_signed_is_refused",
    ] {
        let o = outcome(&report, name);
        assert!(!o.is_verified(), "{name} pairs a typed mask with the other signedness \
                                    (`E0308`) and must be refused, got: {o}");
    }
    for name in [
        "contract_signed_mask_with_signed_partner_reads",
        "contract_unsigned_mask_with_unsigned_partner_reads",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "{name} is well-typed and must verify, got: {o}");
    }
}

/// A pin is *transitive*: a right-hand side that names an earlier pinned variable is
/// pinned too, and the body folds as if the whole chain had been written as literals.
///
/// `a == 5 && b == a + 1 && c == b * 2` fixes `c` at `12` by transitivity, so `c / 4` is
/// `12 / 4` and the obligation is a fact about numbers. A single-pass extraction pinned
/// only `a`, left `b` and `c` symbolic, and built the full divider — `incomplete` however
/// small the contract was. The multiply is the second half of the shape: it makes the
/// *path condition* expensive even once every operand is a literal, which is what the
/// closed-goal check in `prove_implies` exists for.
///
/// The `cannot_prove_this` companion is the point: without it, an engine that answered
/// `Verified` for everything would pass, so the negative is what makes the positive a
/// proof rather than a vacuous `true`.
#[test]
fn a_transitive_pin_chain_folds_the_body() {
    let Some(report) = verify_realistic(&[
        "a_transitive_pin_chain_folds_the_body",
        "a_transitive_pin_chain_cannot_prove_this",
    ]) else {
        return;
    };
    let good = outcome(&report, "a_transitive_pin_chain_folds_the_body");
    assert!(good.is_verified(), "a transitive pin chain must fold the body; got: {good}");
    // The negative must be *refuted*, not merely "not verified". A refusal and a
    // counterexample are both "not verified", and only the second is evidence the
    // rewrite did anything: the point of rewriting the pins into the path is that the
    // multiply leaves the assumption and the false claim becomes decidable. Asserting
    // the weaker property would let a regression back to `incomplete` pass.
    let bad = outcome(&report, "a_transitive_pin_chain_cannot_prove_this");
    assert!(
        matches!(bad, FnOutcome::Failed { .. }),
        "a false claim about a transitively pinned chain must be refuted, not refused; got: {bad}"
    );
}

/// An unsigned division by a power of two is a shift, and the body over a *symbolic*
/// dividend is decided rather than refused for the divider's diagram.
///
/// The signed fast path existed; the unsigned side did not, so `n / 4` on a `u64` with
/// only a bound on `n` built the full restoring divider and came back `incomplete` in
/// ~0.9 s. The remainder is the other half of the same helper (`n & 3`), and it is here so
/// a future edit that wires only the quotient fails.
///
/// The `cannot_prove_this` companion is what keeps "decided" meaning "decided correctly":
/// without it, a fast path that returned a wrong value for every input could still pass.
#[test]
fn an_unsigned_power_of_two_division_is_a_shift_not_a_divider() {
    let Some(report) = verify_realistic(&[
        "an_unsigned_power_of_two_division_is_decided",
        "an_unsigned_power_of_two_division_cannot_prove_this",
        "an_unsigned_power_of_two_remainder_is_decided",
    ]) else {
        return;
    };
    for name in [
        "an_unsigned_power_of_two_division_is_decided",
        "an_unsigned_power_of_two_remainder_is_decided",
    ] {
        let o = outcome(&report, name);
        assert!(o.is_verified(), "an unsigned power-of-two op must be decided; `{name}` got: {o}");
    }
    let bad = outcome(&report, "an_unsigned_power_of_two_division_cannot_prove_this");
    assert!(
        !bad.is_verified(),
        "a false claim about an unsigned division must be refuted; got: {bad}"
    );
}

// ---------------------------------------------------------------------------
// Recursion by contract
// ---------------------------------------------------------------------------

/// A recursive function is proved by induction, not by unrolling.
///
/// The self-call is answered by the function's own contract: its precondition is
/// proved of `n - 1`, the `decreases:` measure is proved to shrink, and the
/// postcondition is assumed for the result. The base case is proved by the body,
/// which is what makes the induction well-founded rather than circular.
///
/// Before `decreases:` existed, this function hit `DEFAULT_INLINE_DEPTH` and came
/// back `Incomplete`, so a proof here is the whole point of the feature.
#[test]
fn a_recursive_function_is_proved_by_its_decreases_measure() {
    let Some(report) = verify_realistic(&["a_recursive_identity"]) else { return };
    let o = outcome(&report, "a_recursive_identity");
    assert!(
        o.is_verified(),
        "a recursive function with a decreasing measure must be proved by induction, got: {o}"
    );
}

/// The inductive assumption must not rescue a body that is simply wrong.
///
/// `a_recursive_lie_cannot_prove_this` has `a_recursive_identity`'s contract but a
/// body that returns `n + 1` in the recursive case. If the postcondition were
/// assumed at the base case too -- or if the `return` obligations were skipped --
/// it would come back `verified`, which is a false proof. It must be a definite
/// failure, with a counterexample.
#[test]
fn a_recursive_body_that_does_not_establish_its_postcondition_is_refuted() {
    let Some(report) = verify_realistic(&["a_recursive_lie_cannot_prove_this"]) else { return };
    let o = outcome(&report, "a_recursive_lie_cannot_prove_this");
    let FnOutcome::Failed { kind, .. } = o else {
        panic!("a recursive body that breaks its postcondition must fail, got: {o}");
    };
    assert_eq!(kind, "postcondition", "got: {o}");
}

/// An assumption with no decreasing measure is circular, so it must be refused.
///
/// `a_recursive_call_that_does_not_decrease_cannot_prove_this` calls itself on the
/// same `n`. Its precondition and postcondition are both true of the body, so
/// nothing but the measure check stands between it and a false proof. It must not
/// verify.
#[test]
fn a_recursive_call_without_a_decreasing_measure_is_not_assumed() {
    let Some(report) = verify_realistic(&["a_recursive_call_that_does_not_decrease_cannot_prove_this"])
    else {
        return;
    };
    let o = outcome(&report, "a_recursive_call_that_does_not_decrease_cannot_prove_this");
    assert!(
        !o.is_verified(),
        "an induction without a decreasing measure must not be assumed, got: {o}"
    );
}

/// The recursive call's *precondition* is an obligation, not a formality.
///
/// `a_recursive_call_out_of_range_cannot_prove_this` has `requires: n <= 3` and
/// calls itself on `n + 1`, leaving that range. Proving the precondition at the
/// call is what keeps the induction hypothesis applicable only where the contract
/// holds; without it the postcondition would be assumed for an input the function
/// never promised anything about.
#[test]
fn a_recursive_call_must_satisfy_its_own_precondition() {
    let Some(report) =
        verify_realistic(&["a_recursive_call_out_of_range_cannot_prove_this"])
    else {
        return;
    };
    let o = outcome(&report, "a_recursive_call_out_of_range_cannot_prove_this");
    assert!(
        !o.is_verified(),
        "a recursive call that violates its own precondition must not be assumed, got: {o}"
    );
}

/// A contract on an *inherent method* is resolved, and its postcondition is
/// actually checked.
///
/// The MIR dump names a method's body `<impl at FILE:L:C: L:C>::bump`, but the
/// source scanner keys the contract by the bare `bump`. Resolving only the exact
/// dump name matched nothing, and a missing contract is not a refusal:
/// `verify_function` derives `requires` and `ensures` from it, so the method was
/// checked against `true` and *no* postcondition and came back `verified` with
/// **zero obligations**. The obligation count is the load-bearing part of this
/// assertion -- a fix that merely matched the name but skipped the body would
/// still report `Verified`, and only the count catches that.
#[test]
fn a_contract_on_an_inherent_method_is_resolved_and_checked() {
    let Some(report) = verify_realistic(&["bump"]) else { return };
    let o = outcome(&report, "bump");
    let FnOutcome::Verified { obligations, .. } = o else {
        panic!("a method whose contract holds must verify, got: {o}");
    };
    assert!(
        *obligations > 0,
        "the method's postcondition must be checked, not silently dropped; got {obligations} \
         obligation(s)"
    );
}

/// The false direction: a method whose postcondition the body does not establish
/// must be refuted, never `verified`.
///
/// `bump_cannot_prove_this` has `bump`'s body but demands `ret == self.n + 2`, so
/// the claim is false on every input. Before the tail resolution this was
/// `Verified { obligations: 0 }` -- a false proof, because the contract never
/// reached the checker. The failure kind is pinned to the postcondition so a fix
/// that refused the method for an unrelated reason cannot pass this.
#[test]
fn a_contract_on_an_inherent_method_that_is_false_is_refuted() {
    let Some(report) = verify_realistic(&["bump_cannot_prove_this"]) else { return };
    let o = outcome(&report, "bump_cannot_prove_this");
    let FnOutcome::Failed { kind, .. } = o else {
        panic!("a method whose postcondition is false must fail, got: {o}");
    };
    assert_eq!(kind, "postcondition", "the failure must be the postcondition, got `{kind}`");
}

// ---------------------------------------------------------------------------
// Frontend soundness regressions (F1-F4)
//
// Each of these four was a confirmed defect in the MIR frontend, found by probe
// and fixed in the same change. They are pinned here so a later refactor cannot
// quietly reopen them.

/// F1: a free function named exactly like an intrinsic that calls the *intrinsic*
/// is not calling itself.
///
/// `wrapping_add` calls `u8::wrapping_add` on its non-base path. The intrinsic is
/// printed fully qualified (`core::num::<impl u8>::wrapping_add`), and the old
/// resolver matched call names to definitions on the last `::` component alone,
/// so the intrinsic call resolved to *this function*. `try_recursive_call` then
/// assumed this function's own postcondition for the result -- a genuine false
/// proof: `ret == 0` was "proved" while the body returns `n` for `n > 0`. The
/// resolver now also requires the method's `self` type to agree, so `u8` and the
/// free function are distinct and the intrinsic model handles the call.
///
/// The name must be the intrinsic's *exact* tail, and the function needs a
/// `decreases:` measure, or the recursion route that carries the false proof never
/// fires -- a name like `wrapping_add_cannot_prove_this` does not reproduce it.
#[test]
fn an_intrinsic_call_is_not_a_self_recursive_call() {
    let Some(report) = verify_realistic(&["wrapping_add"]) else { return };
    let o = outcome(&report, "wrapping_add");
    let FnOutcome::Failed { kind, .. } = o else {
        panic!(
            "a function named like an intrinsic that calls the intrinsic must be \
             refuted, not proved from its own postcondition; got: {o}"
        );
    };
    assert_eq!(kind, "postcondition", "the failure must be the postcondition, got `{kind}`");
}

/// F1 companion: a free function named like an intrinsic that *does* recurse must
/// still be proved by induction.
///
/// The guard that fixes F1 must not refuse a real self-call just because the name
/// matches an intrinsic. `wrapping_add_still_recurses` calls itself, printed bare
/// (`wrapping_add_still_recurses`), which matches it by exact name.
#[test]
fn a_free_recursion_named_like_an_intrinsic_still_recurses() {
    let Some(report) = verify_realistic(&["wrapping_add_still_recurses"]) else { return };
    let o = outcome(&report, "wrapping_add_still_recurses");
    assert!(
        o.is_verified(),
        "a free function named like an intrinsic that recurses must verify; got: {o}"
    );
}

/// F1 companion: a *static associated function* named like an intrinsic that
/// genuinely recurses must still be proved by induction.
///
/// The type check that fixes F1 must not refuse a real self-call just because the
/// tail matches an intrinsic name. `Recursing::wrapping_sub` calls itself, and a
/// `core` intrinsic's call name carries an `<impl` projection that the resolver
/// refuses, so the real self-call still fires.
#[test]
fn a_method_named_like_an_intrinsic_still_recurses() {
    let Some(report) = verify_realistic(&["wrapping_sub"]) else { return };
    let o = outcome(&report, "wrapping_sub");
    assert!(o.is_verified(), "a method named like an intrinsic that recurses must verify; got: {o}");
}

/// F4: a recursive call evaluates the callee's contract with the entry `const`
/// table, so a contract naming a constant resolves at the self-call.
///
/// `a_recursive_contract_naming_a_const_is_resolved` names `LIMIT` in both its
/// `requires` and its `ensures`. The recursive call rebuilt the contract
/// environment from `FieldEnv::default()`, whose `const` table is empty, so the
/// `requires` was unreadable *at the self-call* and the whole function came back
/// `Skipped` -- a lost proof. The call site now carries the entry constants.
#[test]
fn a_recursive_contract_naming_a_const_is_resolved() {
    let Some(report) = verify_realistic(&["a_recursive_contract_naming_a_const_is_resolved"])
    else {
        return;
    };
    let o = outcome(&report, "a_recursive_contract_naming_a_const_is_resolved");
    assert!(
        o.is_verified(),
        "a recursive contract naming a crate-level const must resolve at the self-call; got: {o}"
    );
}

/// F3: a crate-level `const` a *contract* names but no body uses is kept.
///
/// The dump's bare-use test is silent for a constant with no use site at all, so
/// the definition was dropped and the contract went unreadable -- a lost proof.
/// The source says the item is module-scoped, and `spec::crate_level_consts`
/// carries that to the parser.
#[test]
fn a_contract_only_const_is_resolved() {
    let Some(report) = verify_realistic(&["a_contract_only_const_is_resolved"]) else { return };
    let o = outcome(&report, "a_contract_only_const_is_resolved");
    assert!(
        o.is_verified(),
        "a crate-level const named only by a contract must resolve; got: {o}"
    );
}

/// F2: a string literal that spells `const NAME` must not leak a function-local
/// `const` into the program-wide table.
///
/// The bare-use scan reads `const NAME` out of the dump to tell a crate-level
/// constant from a function-local one. A `debug s => const "const LEAKY";`
/// binding and the `alloc` block behind the string spell those letters as *data*,
/// so a scan of the raw line saw a use and gave the local `LEAKY` a program-wide
/// key -- reopening the exact false proof
/// `a_local_const_is_not_in_scope_in_another_function` guards. The scan now drops
/// string literals and skips `alloc` blocks, so the contract's `LEAKY` resolves to
/// nothing and the function is `Skipped`, never `Verified`.
///
/// The local name is *unique* among the file's locals, which is what makes rustc
/// print its definition bare (`const LEAKY`) -- the spelling that collides with a
/// crate-level item. A name shared by two locals is printed qualified and does not
/// reproduce the shape.
#[test]
fn a_string_literal_does_not_leak_a_local_const() {
    let Some(report) =
        verify_realistic(&["a_string_literal_must_not_leak_a_unique_local_const"])
    else {
        return;
    };
    let o = outcome(&report, "a_string_literal_must_not_leak_a_unique_local_const");
    assert!(
        !o.is_verified(),
        "a string literal must not leak a function-local const into a contract; got: {o}"
    );
}
