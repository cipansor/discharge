//! The end-to-end driver: source in, verdicts out.
//!
//! This is the layer that ties the three stages together and owns the two
//! things the other modules cannot know about: how to get MIR out of `rustc`,
//! and how to decide *which* functions to verify. It is also where the honesty
//! of the whole frontend is enforced, in one rule:
//!
//! > A function is reported verified only when every obligation was proved
//! > *and* every path was explored. A cutoff is reported as a cutoff.
//!
//! That rule is why [`FnOutcome`] has a distinct `Incomplete` state instead of
//! folding cutoffs into `Verified`.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;

use crate::mir::exec;
use crate::mir::parse::{self, MirFn, MirProgram};

// The report types are part of the public verdict surface -- `FnOutcome`
// carries a `MirReport` -- so they are re-exported here rather than leaving a
// crate-internal type in a public signature.
pub use crate::mir::exec::{MirReport, Obligation, ObligationKind};
use crate::mir::spec::{self, SpecError, Specs};
use crate::smt::{self, Verdict};

/// Where the MIR text came from, so failures can say so.
#[derive(Clone, Debug)]
pub enum MirSource {
    /// `rustc --emit=mir` on this file.
    Emitted {
        /// The Rust source the MIR was emitted from.
        file: PathBuf,
        /// The MIR text `rustc` printed.
        mir: String,
    },
    /// A pre-generated dump, which lets a build without nightly reuse one.
    File(PathBuf),
    /// Dump text supplied directly, for tests.
    Inline(String),
}

/// Get MIR text for a Rust file, or explain why not.
///
/// `rustc --emit=mir` requires nightly; the error is returned rather than
/// papered over, because "the frontend could not run" and "the code is wrong"
/// must never be reported the same way.
///
/// The compiler is taken from `DISCHARGE_RUSTC` when set, and otherwise from
/// `rustc` on `PATH`. The dedicated variable exists so that pointing this tool
/// at a nightly does not disturb the `rustc` that cargo is using to build the
/// test suite -- setting `RUSTC` would do exactly that.
pub fn emit_mir(file: &Path) -> Result<String, String> {
    let rustc = std::env::var("DISCHARGE_RUSTC").unwrap_or_else(|_| "rustc".into());
    emit_mir_with(&rustc, file)
}

/// [`emit_mir`] with the compiler named explicitly.
///
/// This exists so a test can point at a nightly toolchain without mutating the
/// process environment, which is a race when tests run in parallel.
pub fn emit_mir_with(rustc: &str, file: &Path) -> Result<String, String> {
    // `rustc` writes its intermediate artifacts next to the output path, so the
    // output goes to a temp file rather than to `/dev/stdout` -- pointing it at
    // `/dev` makes rustc try to create a temp directory there and fail.
    // The name must be unique per *call*, not just per process: tests run in
    // parallel threads of one process, and a shared name means one test deletes
    // the file another is about to read.
    static SEQ: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
    let seq = SEQ.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
    let out_path = std::env::temp_dir().join(format!(
        "discharge-mir-{}-{}-{}.mir",
        std::process::id(),
        seq,
        file.file_stem().map(|s| s.to_string_lossy().into_owned()).unwrap_or_default()
    ));
    let out = Command::new(rustc)
        .arg("--crate-type=lib")
        .arg("--emit=mir")
        .arg("-o")
        .arg(&out_path)
        .arg(file)
        .output()
        .map_err(|e| format!("could not run rustc: {e}"))?;
    if !out.status.success() {
        return Err(format!(
            "rustc failed on {}: {}",
            file.display(),
            String::from_utf8_lossy(&out.stderr).trim()
        ));
    }
    let text = std::fs::read_to_string(&out_path).map_err(|e| {
        format!(
            "rustc produced no MIR for {} ({e}); `--emit=mir` needs a nightly toolchain",
            file.display()
        )
    })?;
    let _ = std::fs::remove_file(&out_path);
    if text.trim().is_empty() {
        return Err(format!(
            "rustc produced empty MIR for {}; `--emit=mir` needs a nightly toolchain",
            file.display()
        ));
    }
    Ok(text)
}

/// What happened to one function.
#[derive(Clone, Debug)]
pub enum FnOutcome {
    /// Every obligation proved and every path explored.
    Verified {
        /// How many obligations were discharged.
        obligations: usize,
        /// How many of those were rustc-emitted panic conditions.
        panics_ruled_out: usize,
    },
    /// A definite failure, with the obligation that failed.
    Failed {
        /// Which obligation failed, e.g. `panic: attempt to compute ...`.
        kind: String,
        /// The counterexample, as variable assignments.
        detail: String,
    },
    /// Not decided: a budget, an unmodelled construct, or an open obligation.
    /// This is *not* a pass.
    Incomplete {
        /// The obligations that were discharged before the path was cut short.
        report: Box<MirReport>,
        /// Why the verification is incomplete: budgets, unmodelled constructs,
        /// or obligations the engine could not decide.
        reasons: Vec<String>,
    },
    /// The function was skipped, with the reason.
    Skipped {
        /// Why the function was not verified at all.
        reason: String,
    },
}

impl FnOutcome {
    /// True only for [`FnOutcome::Verified`]. `Incomplete` is not a pass.
    pub fn is_verified(&self) -> bool {
        matches!(self, FnOutcome::Verified { .. })
    }
}

impl std::fmt::Display for FnOutcome {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            FnOutcome::Verified { obligations, panics_ruled_out } => write!(
                f,
                "verified ({obligations} obligation(s), {panics_ruled_out} panic(s) ruled out)"
            ),
            FnOutcome::Failed { kind, detail } => write!(f, "FAILED: {kind} — {detail}"),
            FnOutcome::Incomplete { reasons, .. } => {
                write!(f, "incomplete ({} reason(s))", reasons.len())?;
                for r in reasons.iter().take(3) {
                    write!(f, "\n      - {r}")?;
                }
                Ok(())
            }
            FnOutcome::Skipped { reason } => write!(f, "skipped: {reason}"),
        }
    }
}

/// Verify one function from a parsed program plus its source contracts.
pub fn verify_function(prog: &MirProgram, f: &MirFn, specs: &Specs) -> FnOutcome {
    let contract = specs.get(&f.name);
    let arg_vars = spec::arg_vars(f);
    let signed = spec::signed_args(f);
    let ret_signed = f.ret_ty.is_signed();

    // Build the precondition. No contract means `true`, which is the right
    // default: a function with no `requires` is checked for panic freedom on
    // every input.
    let mut pre = None;
    if let Some(c) = contract {
        for r in &c.requires {
            match spec::eval_requires(r, &arg_vars, &signed) {
                Ok(p) => pre = Some(match pre {
                    None => p,
                    Some(prev) => smt::and(prev, p),
                }),
                Err(e) => {
                    return FnOutcome::Skipped {
                        reason: format!("unreadable `requires`: {e}"),
                    }
                }
            }
        }
    }

    // Build the postcondition as a closure over the return value.
    let ensures: Vec<String> = contract.map(|c| c.ensures.clone()).unwrap_or_default();
    let args_for_post = arg_vars.clone();
    let post = if ensures.is_empty() {
        None
    } else {
        Some(move |ret| {
            let mut acc: Option<crate::smt::Pred> = None;
            for e in &ensures {
                if let Ok(p) = spec::eval_ensures(e, &args_for_post, ret, &signed, ret_signed) {
                    acc = Some(match acc {
                        None => p,
                        Some(prev) => smt::and(prev, p),
                    });
                }
            }
            acc.unwrap_or_else(|| smt::truth(true))
        })
    };

    let report = exec::verify_fn(prog, f, pre, post);

    // A definite failure outranks incompleteness: a counterexample is a result.
    if let Some((kind, cex)) = report.counterexample() {
        return FnOutcome::Failed { kind: kind.to_string(), detail: cex.to_string() };
    }
    if report.undecided() > 0 {
        let mut reasons = report.unknown_paths.clone();
        reasons.push(format!("{} obligation(s) the engine could not decide", report.undecided()));
        return FnOutcome::Incomplete { report: Box::new(report), reasons };
    }
    if !report.unknown_paths.is_empty() {
        return FnOutcome::Incomplete {
            reasons: report.unknown_paths.clone(),
            report: Box::new(report),
        };
    }
    FnOutcome::Verified {
        obligations: report.obligations.len(),
        panics_ruled_out: report.panics_ruled_out(),
    }
}

/// The result for a whole file.
#[derive(Clone, Debug, Default)]
pub struct FileReport {
    /// The file these results are about.
    pub source: PathBuf,
    /// One outcome per verified function, in contract order.
    pub outcomes: Vec<(String, FnOutcome)>,
    /// Functions that carried a contract but were not found in the MIR. A
    /// non-empty list means the run covered less than the contracts asked for.
    pub missing: Vec<String>,
}

impl FileReport {
    /// How many functions were fully verified.
    pub fn verified(&self) -> usize {
        self.outcomes.iter().filter(|(_, o)| o.is_verified()).count()
    }

    /// How many functions had a definite counterexample.
    pub fn failed(&self) -> usize {
        self.outcomes.iter().filter(|(_, o)| matches!(o, FnOutcome::Failed { .. })).count()
    }

    /// How many functions were left undecided.
    pub fn incomplete(&self) -> usize {
        self.outcomes.iter().filter(|(_, o)| matches!(o, FnOutcome::Incomplete { .. })).count()
    }

    /// True only when nothing failed, nothing was incomplete, and every
    /// contracted function was found. A skipped function is not a pass either.
    pub fn is_clean(&self) -> bool {
        self.failed() == 0 && self.incomplete() == 0 && self.missing.is_empty()
    }
}

/// Verify every contracted function in one source file.
///
/// `only` restricts the run to the named functions, which is what a per-file
/// contract test wants: verifying the whole file on every call would be slow and
/// would report unrelated functions.
pub fn verify_file(source: &Path, only: &[String]) -> Result<FileReport, String> {
    let rustc = std::env::var("DISCHARGE_RUSTC").unwrap_or_else(|_| "rustc".into());
    verify_file_with(&rustc, source, only)
}

/// [`verify_file`] with the compiler named explicitly. See [`emit_mir_with`].
pub fn verify_file_with(
    rustc: &str,
    source: &Path,
    only: &[String],
) -> Result<FileReport, String> {
    let text = std::fs::read_to_string(source)
        .map_err(|e| format!("could not read {}: {e}", source.display()))?;
    let specs = spec::extract(&text);
    let mir = emit_mir_with(rustc, source)?;
    let prog = parse::parse_program(&mir);

    let mut report = FileReport { source: source.to_path_buf(), ..Default::default() };

    // Every contracted function must exist in the dump; a contract naming a
    // function that is not there is a coverage hole, not a silent pass.
    for name in specs.by_fn.keys() {
        if prog.get(name).is_none() {
            report.missing.push(name.clone());
        }
    }

    let wanted: Vec<String> = if only.is_empty() {
        specs.by_fn.keys().cloned().collect()
    } else {
        only.to_vec()
    };

    for name in wanted {
        let Some(f) = prog.get(&name) else {
            continue;
        };
        let outcome = smt::with_fresh(|| verify_function(&prog, f, &specs));
        report.outcomes.push((name, outcome));
    }
    Ok(report)
}

/// Verify a whole MIR dump, using contracts from a companion source file.
pub fn verify_mir_text(
    mir: &str,
    specs: &Specs,
    only: &[String],
) -> Result<FileReport, String> {
    let prog = parse::parse_program(mir);
    let mut report = FileReport::default();
    for name in specs.by_fn.keys() {
        if prog.get(name).is_none() {
            report.missing.push(name.clone());
        }
    }
    let wanted: Vec<String> = if only.is_empty() {
        specs.by_fn.keys().cloned().collect()
    } else {
        only.to_vec()
    };
    for name in wanted {
        let Some(f) = prog.get(&name) else { continue };
        let outcome = smt::with_fresh(|| verify_function(&prog, f, specs));
        report.outcomes.push((name, outcome));
    }
    Ok(report)
}

/// A helper for tests and tools: parse a dump and return function names.
pub fn function_names(mir: &str) -> Vec<String> {
    parse::parse_program(mir).fns.iter().map(|f| f.name.clone()).collect()
}

/// Map from name to parsed function, for callers that want to inspect the IR.
pub fn functions(mir: &str) -> BTreeMap<String, MirFn> {
    parse::parse_program(mir)
        .fns
        .into_iter()
        .map(|f| (f.name.clone(), f))
        .collect()
}

/// The `Verdict` for a predicate, as a convenience for callers that want to ask
/// a one-off question of the engine under the same arena discipline.
pub fn decide(p: crate::smt::Pred) -> Verdict {
    smt::with_fresh(|| smt::prove(p))
}

/// Re-exported so a caller can name the error type without reaching into `spec`.
pub type ContractError = SpecError;
