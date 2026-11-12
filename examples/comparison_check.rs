//! The comparison fixtures' gate, as a driver rather than a scoreboard scrape.
//!
//! `tools/comparison/run.sh` used to assert the *coverage* line
//! (`decided 0 of 1`) for each injected bug. That line counts only
//! `FnOutcome::Verified`, so `Failed`, `Incomplete` and `Skipped` all leave it at
//! zero -- which means a fixture whose contract became *unreadable* would still
//! read `decided 0 of 1` and the gate would call it a caught defect while having
//! no counterexample at all. That is the "teeth have to isolate the guard they
//! claim to test" rule violated by the gate that enforces it: a rejection test
//! that cannot tell a refutation from a lost proof is not a rejection test.
//!
//! So the assertion here is on the per-function [`FnOutcome`], not on a count:
//!
//!   * the positive fixture must carry a contract for *each* function it claims
//!     and be `Verified` for every one of them. The names are pinned here rather
//!     than read from `spec::extract`, because a name read from the contracts
//!     disappears with the contract: deleting one function's contract would
//!     shrink the request list, the remaining functions would pass, and the gate
//!     would report success for a claim it never checked;
//!   * each bug fixture must be `Failed` with the *exact* obligation kind -- the
//!     `+` overflow for the swapped `sat_add`, the postcondition for the
//!     wrong-arm `clamp`, the loop invariant for the wrong-body `sum_to`. The
//!     whole kind, not a `panic` prefix: a prefix accepts *any* panic, so a
//!     divide-by-zero before the addition would satisfy a test about an overflow;
//!   * `Incomplete` and `Skipped` are refusals of the *fixture*, not evidence
//!     about the defect, so they fail the run and say which one they were;
//!   * the degenerate implementations (whole-function contracts mean they must
//!     be refused) are checked the same way.
//!
//! `Failed` with the wrong kind is also a failure: a fixture that trips the
//! wrong obligation is not testing what it claims, which is exactly the trap the
//! old `n <= 8` Coq theorem fell into.
//!
//! Exit status: 0 every claim held, 1 a claim did not hold, 2 no usable
//! `VERIF_RUSTC` (reported and skipped by the caller, like the other gates).
//!
//! Run it with a nightly named:
//!
//! ```console
//! $ VERIF_RUSTC=$(rustup which --toolchain nightly rustc) \
//!     cargo run --features std --example comparison_check
//! ```

use std::path::{Path, PathBuf};

use verif::mir::spec;
use verif::mir::verify::{self, FnOutcome};

/// What one fixture must produce.
enum Want {
    /// Each named function must carry *exactly* the pinned contract, clause by
    /// clause, and be `Verified`.
    ///
    /// The clauses are pinned, and none of them is read back from the fixture. A
    /// name alone is not enough: a `requires`-only contract is still a contract,
    /// so a fixture that lost every `ensures:` would keep its name, shrink to
    /// panic-freedom, and come back `Verified` with the claimed result never
    /// checked. So the *clauses* are the claim, and the claim is what is pinned.
    ///
    /// The text is pinned rather than a count, because a count cannot tell a
    /// whole-function contract from a weakened one: swapping `sat_add`'s
    /// `ret == a + b` for `ret >= a` keeps the number of clauses and drops the part
    /// that says what the function computes. The same holds for `requires:` --
    /// loosening `n <= 8` to `n <= 2` proves a strictly smaller statement -- so the
    /// precondition and the loop invariant are pinned too, not just the result.
    /// This is the reason the fixtures exist at all (the bounds-only contracts were
    /// the first version's bug), so the gate has to hold the whole statement, not
    /// merely count it.
    Verified(&'static [(&'static str, Contract)]),
    /// The named function fails, and its obligation kind is *exactly* this text.
    ///
    /// Exact rather than a prefix: a `panic` prefix would accept any panic, so a
    /// divide-by-zero before the addition would pass a test about an overflow.
    Failed {
        /// The function the claim is about.
        function: &'static str,
        /// The exact obligation kind the failure must name.
        kind: &'static str,
    },
}

/// A contract, clause for clause, as it must appear in the fixture.
///
/// Every clause kind the engine reads is here, because each one can be weakened
/// independently and a weaker contract is a weaker claim: dropping an `ensures:`
/// leaves panic freedom, and loosening a `requires:` proves a smaller statement.
#[derive(Debug)]
struct Contract {
    requires: &'static [&'static str],
    ensures: &'static [&'static str],
    invariants: &'static [&'static str],
}

/// One fixture: its path, and the claim it is evidence for.
struct Fixture {
    path: &'static str,
    want: Want,
    /// What the fixture is, for the failure message.
    why: &'static str,
}

const ROOT: &str = "examples/comparison";

/// The exact panic text for the guarded addition in `sat_add`.
///
/// It is rustc's own wording (`src/mir/shape.rs` maps it to `PanicKind::OverflowAdd`),
/// spelled out because the claim is about *this* overflow and not about panics in
/// general.
const OVERFLOW_ADD: &str = "panic: attempt to compute `{} + {}`, which would overflow";

/// The positive fixture's contracts, clause for clause and in source order.
///
/// These are the claim under test. They are copied here rather than read from
/// `spec::extract` so that weakening the fixture -- dropping a clause, dropping the
/// result and keeping only the bounds, or loosening a precondition -- is a
/// *failure* here and not a quietly smaller success.
const SAT_ADD_CONTRACT: Contract = Contract {
    requires: &["true"],
    ensures: &[
        "ret >= a",
        "ret >= b",
        "a <= 65535u16 - b || ret == 65535u16",
        "a > 65535u16 - b || ret == a + b",
    ],
    invariants: &[],
};
const CLAMP_CONTRACT: Contract = Contract {
    requires: &["lo <= hi"],
    ensures: &[
        "!(x < lo) || ret == lo",
        "!(lo <= x && x > hi) || ret == hi",
        "!(lo <= x && x <= hi) || ret == x",
    ],
    invariants: &[],
};
const SUM_TO_CONTRACT: Contract = Contract {
    requires: &["n <= 8"],
    ensures: &["ret == n"],
    invariants: &["i <= n && s == i"],
};

/// The fixtures, as data, so the driver and the shell script cannot disagree
/// about which files are checked or what each one must do.
fn fixtures() -> Vec<Fixture> {
    vec![
        Fixture {
            path: "target.rs",
            want: Want::Verified(&[
                ("sat_add", SAT_ADD_CONTRACT),
                ("clamp", CLAMP_CONTRACT),
                ("sum_to", SUM_TO_CONTRACT),
            ]),
            why: "the positive fixture: the same three functions every tool proves",
        },
        Fixture {
            path: "bugs/target.rs",
            want: Want::Failed {
                function: "sat_add",
                kind: OVERFLOW_ADD,
            },
            why: "swapped branches, so the guarded `+` is the one that can overflow",
        },
        Fixture {
            path: "bugs/clamp.rs",
            want: Want::Failed {
                function: "clamp",
                kind: "postcondition",
            },
            why: "returns `hi` below the range, so the contract's first disjunct is false",
        },
        Fixture {
            path: "bugs/loop.rs",
            want: Want::Failed {
                function: "sum_to",
                kind: "loop invariant preserved",
            },
            why: "the loop body adds two, so the invariant is not preserved",
        },
    ]
}

fn main() {
    let rustc = match std::env::var("VERIF_RUSTC") {
        Ok(r) if !r.trim().is_empty() => r,
        _ => {
            eprintln!("comparison_check: set VERIF_RUSTC to a nightly `rustc`");
            std::process::exit(2);
        }
    };

    let mut failures: Vec<String> = Vec::new();
    let mut checked = 0usize;

    for f in fixtures() {
        let path = PathBuf::from(ROOT).join(f.path);
        checked += 1;
        match check_one(&rustc, &path, &f) {
            Ok(line) => println!("ok   {:<20} {line}", f.path),
            Err(why) => {
                println!("FAIL {:<20} {why}", f.path);
                failures.push(format!("{}: {why}", f.path));
            }
        }
    }

    for (name, src) in degenerate() {
        checked += 1;
        let tmp = write_scratch(&name, &src);
        let why = "degenerate implementation the whole-function contract must refuse";
        let r = check_failed(&rustc, &tmp, &name, "postcondition", why);
        // Remove the scratch file only once its MIR has been emitted, which
        // `check_failed` has done by the time it returns. A concurrent gate uses
        // its own path, so it never sees this removal.
        let _ = std::fs::remove_file(&tmp);
        match r {
            Ok(line) => println!("ok   {:<20} {line}", format!("degenerate/{name}")),
            Err(why) => {
                println!("FAIL {:<20} {why}", format!("degenerate/{name}"));
                failures.push(format!("degenerate/{name}: {why}"));
            }
        }
    }

    println!("\nchecked {checked} fixture(s)");
    if failures.is_empty() {
        println!("every comparison claim held");
    } else {
        println!("\nUNEXPECTED:");
        for f in &failures {
            println!("  {f}");
        }
        std::process::exit(1);
    }
}

/// Run one fixture and check its outcome against `f.want`.
fn check_one(rustc: &str, path: &Path, f: &Fixture) -> Result<String, String> {
    match &f.want {
        Want::Verified(expected) => check_verified(rustc, path, expected),
        Want::Failed { function, kind } => check_failed(rustc, path, function, kind, f.why),
    }
}

/// Assert that each pinned name carries exactly its pinned contract and is
/// `Verified`.
fn check_verified(
    rustc: &str,
    path: &Path,
    expected: &[(&str, Contract)],
) -> Result<String, String> {
    let text = std::fs::read_to_string(path)
        .map_err(|e| format!("cannot read {}: {e}", path.display()))?;
    let specs = spec::extract(&text);
    let mir = verify::emit_mir_with(rustc, path).map_err(|e| format!("could not get MIR: {e}"))?;

    // The claim is the clause text, so every clause is compared -- not the presence
    // of a contract and not the number of clauses. A name alone passes a
    // `requires`-only contract; a count alone passes a weakened one; and each kind
    // can be weakened on its own, so all three are checked.
    for (name, want) in expected {
        let Some(found) = resolve_contract(&specs, name) else {
            return Err(format!(
                "`{name}` carries no contract in the fixture, so the positive claim would go \
                 unchecked"
            ));
        };
        if found.ensures.is_empty() {
            return Err(format!(
                "`{name}` carries a contract but no `ensures:`, so only panic freedom would be \
                 checked -- the claimed result would go unchecked"
            ));
        }
        compare_clauses(name, "requires", want.requires, &found.requires)?;
        compare_clauses(name, "ensures", want.ensures, &found.ensures)?;
        compare_clauses(name, "invariant", want.invariants, &found.invariants)?;
    }

    let wanted: Vec<String> = expected.iter().map(|(n, _)| n.to_string()).collect();
    let report =
        verify::verify_mir_text(&mir, &specs, &wanted).map_err(|e| format!("driver error: {e}"))?;
    if !report.missing.is_empty() {
        return Err(format!(
            "contracted but absent from the MIR: {:?}",
            report.missing
        ));
    }
    // One outcome per expected function: fewer means one was not checked, more
    // means the request matched something it should not have.
    if report.outcomes.len() != expected.len() {
        return Err(format!(
            "expected {} outcome(s) for {:?}, got {} ({:?})",
            expected.len(),
            expected.iter().map(|(n, _)| *n).collect::<Vec<_>>(),
            report.outcomes.len(),
            report
                .outcomes
                .iter()
                .map(|(n, _)| n.as_str())
                .collect::<Vec<_>>()
        ));
    }
    for (want, _) in expected {
        let Some((name, outcome)) = report.outcomes.iter().find(|(n, _)| names_match(n, want))
        else {
            return Err(format!("`{want}` has no outcome in the report"));
        };
        match outcome {
            FnOutcome::Verified { .. } => {}
            // The three refusals are named separately: "skipped" is a contract
            // that could not be read and "incomplete" is a budget or an unmodelled
            // construct, and neither is evidence that the code is right *or* wrong.
            FnOutcome::Failed { kind, detail } => {
                return Err(format!(
                    "{name}: expected Verified, got FAILED ({kind} — {detail})"
                ));
            }
            FnOutcome::Incomplete { reasons, .. } => {
                return Err(format!(
                    "{name}: incomplete, so not verified ({})",
                    reasons.join("; ")
                ));
            }
            FnOutcome::Skipped { reason } => {
                return Err(format!("{name}: skipped, so never checked ({reason})"));
            }
        }
    }
    Ok(format!("{} function(s) verified", expected.len()))
}

/// Assert that `function` fails with exactly the obligation kind `want_kind`.
fn check_failed(
    rustc: &str,
    path: &Path,
    function: &str,
    want_kind: &str,
    why: &str,
) -> Result<String, String> {
    let text = std::fs::read_to_string(path)
        .map_err(|e| format!("cannot read {}: {e}", path.display()))?;
    let specs = spec::extract(&text);
    let mir = verify::emit_mir_with(rustc, path).map_err(|e| format!("could not get MIR: {e}"))?;

    let only = vec![function.to_string()];
    let report =
        verify::verify_mir_text(&mir, &specs, &only).map_err(|e| format!("driver error: {e}"))?;
    if !report.missing.is_empty() {
        return Err(format!(
            "contracted but absent from the MIR: {:?}",
            report.missing
        ));
    }
    if report.outcomes.len() != 1 {
        return Err(format!(
            "expected exactly one outcome for `{function}`, got {} ({:?})",
            report.outcomes.len(),
            report
                .outcomes
                .iter()
                .map(|(n, _)| n.as_str())
                .collect::<Vec<_>>()
        ));
    }
    let (name, outcome) = &report.outcomes[0];
    match outcome {
        FnOutcome::Failed { kind, detail } => {
            if kind == want_kind {
                Ok(format!("{name}: FAILED — {kind} (witness: {detail})"))
            } else {
                Err(format!(
                    "{name}: failed on the WRONG obligation: expected `{want_kind}`, got `{kind}` \
                     -- the fixture is not testing what it claims ({why})"
                ))
            }
        }
        // These used to read `decided 0 of 1` and pass. A skipped fixture is a
        // lost proof, not a refutation.
        FnOutcome::Skipped { reason } => Err(format!(
            "{name}: SKIPPED, so the contract was never refuted -- the fixture is a lost proof, \
             not a caught defect ({reason})"
        )),
        FnOutcome::Incomplete { reasons, .. } => Err(format!(
            "{name}: INCOMPLETE, so no counterexample was found -- the fixture is a lost proof, \
             not a caught defect ({})",
            reasons.join("; ")
        )),
        FnOutcome::Verified { .. } => Err(format!(
            "{name}: VERIFIED, so the defect was not caught at all"
        )),
    }
}

/// Fail if a clause kind does not match, naming the kind and both texts.
///
/// The comparison is exact and ordered, so a weakened clause, a dropped clause, a
/// reordered pair and an extra clause are each a failure rather than a smaller
/// success.
fn compare_clauses(name: &str, kind: &str, want: &[&str], found: &[String]) -> Result<(), String> {
    if want == found {
        return Ok(());
    }
    Err(format!(
        "`{name}` states a different `{kind}:` than the one claimed:\n    \
         expected: {want:?}\n    found:    {found:?}"
    ))
}

/// The contract for `name`, by an exact key or a bare `::`-tail.
///
/// Mirrors the lookup `verify::select` uses, so the clause the driver pins is the
/// clause the engine was handed.
fn resolve_contract<'a>(specs: &'a spec::Specs, name: &str) -> Option<&'a spec::FnContract> {
    if let Some(c) = specs.by_fn.get(name) {
        return Some(c);
    }
    specs
        .by_fn
        .iter()
        .find(|(k, _)| names_match(k, name))
        .map(|(_, c)| c)
}

/// Whether a report key names `want`, by the same rules `verify::select` uses: an
/// exact key, or a bare `::`-tail.
fn names_match(key: &str, want: &str) -> bool {
    key == want || key.rsplit("::").next() == Some(want)
}

/// The degenerate implementations the whole-function contracts must refuse.
///
/// `u16::MAX` for every input satisfies `ret >= a && ret >= b`; `lo` for every
/// input satisfies `lo <= ret <= hi`. Both passed the bounds-only contracts the
/// first version of this directory shipped, so they are the evidence that the
/// contracts now state the whole function.
fn degenerate() -> Vec<(String, String)> {
    vec![
        (
            "sat_add".to_string(),
            "/// requires: true\n\
             /// ensures: ret >= a\n\
             /// ensures: ret >= b\n\
             /// ensures: a <= 65535u16 - b || ret == 65535u16\n\
             /// ensures: a > 65535u16 - b || ret == a + b\n\
             pub fn sat_add(a: u16, b: u16) -> u16 { 65535u16 }\n"
                .to_string(),
        ),
        (
            "clamp".to_string(),
            "/// requires: lo <= hi\n\
             /// ensures: !(x < lo) || ret == lo\n\
             /// ensures: !(lo <= x && x > hi) || ret == hi\n\
             /// ensures: !(lo <= x && x <= hi) || ret == x\n\
             pub fn clamp(x: u16, lo: u16, hi: u16) -> u16 { lo }\n"
                .to_string(),
        ),
    ]
}

/// Write a scratch fixture to a path unique *per call*, and return it.
///
/// Unique per call, not per name: two gates running at once would otherwise share
/// one file, and the first to finish would remove it while the second's `rustc`
/// was still opening it -- a valid gate failing for a scheduling reason. This
/// mirrors `verify::emit_mir_with`, which names its temp MIR per call for the
/// same reason. The caller removes the file once its MIR has been emitted.
fn write_scratch(name: &str, src: &str) -> PathBuf {
    use std::sync::atomic::{AtomicU64, Ordering};
    static SEQ: AtomicU64 = AtomicU64::new(0);
    let seq = SEQ.fetch_add(1, Ordering::Relaxed);
    let path = std::env::temp_dir().join(format!(
        "verif-comparison-{}-{seq}-{name}.rs",
        std::process::id()
    ));
    std::fs::write(&path, src).expect("write scratch fixture");
    path
}
