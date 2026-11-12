//! The frontend's proof-of-work: real Rust functions, verified from their MIR.
//!
//! Run with: `cargo run --features std --example mir_demo`
//!
//! The functions under test live in `examples/mir_targets/actuator.rs`, which
//! does not import `verif` at all. Contracts are doc comments
//! (`requires:` / `ensures:` lines); the *bodies* are read from the MIR that
//! `rustc` lowers them to. Nothing is re-modelled by hand, which is the whole
//! point — the earlier frontends in this crate proved things about expressions
//! written next to the code, and a human had to keep the two in step.
//!
//! Set `VERIF_RUSTC` to a nightly `rustc`, since `--emit=mir` needs one:
//!
//! ```text
//! VERIF_RUSTC=$(rustup which --toolchain nightly rustc) \
//!   cargo run --features std --example mir_demo
//! ```

use verif::mir::verify::{self, FnOutcome};

const TARGET: &str = "examples/mir_targets/actuator.rs";

/// What each function is expected to produce.
///
/// `Incomplete` is a first-class expectation, not a failure of the demo. It is
/// what an honest bounded checker returns when the query is beyond its engine,
/// and saying so is the point. `sat_mul` used to be the example of that -- its
/// `u16` guard is a statement about a 32-bit product -- but the multiply-overflow
/// test is now the exact division form (`y != 0 && x > MAX / y`), which the
/// divider decides and which folds against the guard, so it is `Verified`.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Expect {
    Verified,
    Failed,
    Incomplete,
}

/// The expectations, stated as data so the demo and the test suite share them.
pub fn expectations() -> [(&'static str, Expect); 24] {
    use Expect::*;
    [
        ("clamp", Verified),
        ("rate_limit", Verified),
        ("sat_add", Verified),
        ("sat_sub", Verified),
        ("shift_const", Verified),
        // The guard is the caller's here, and rustc's own `assert(n < 16)` still
        // reports `n == 16` as a panic, so this must fail.
        ("shift_left", Failed),
        ("sat_shift", Verified),
        // The guard is `b != 0 && a > u16::MAX / b`, which *is* the exact unsigned
        // multiply-overflow predicate, so the path into `a * b` refutes the overflow
        // obligation without the 32-bit product ever being built.
        ("sat_mul", Verified),
        ("unchecked_add", Failed),
        ("unchecked_sub", Failed),
        ("unchecked_div", Failed),
        ("unchecked_mul", Failed),
        // The guard prevents the overflow, so there is no panic — but the
        // `ensures` is wrong, and a postcondition obligation catches that.
        // This is the case that shows the check is not only about panics.
        ("off_by_one_guard", Failed),

        // --- signed arithmetic ---------------------------------------------
        // These pin the signed/unsigned split. The unsigned cases above cannot
        // tell `<` on `i32` from `<` on `u32`, so a comparison that read the
        // wrong one would still pass every one of them.
        ("clamp_signed", Verified),
        // A guard that excludes both division traps: zero and `MIN / -1`.
        ("checked_div_signed", Verified),
        // No guard at all, so the zero divisor is reachable.
        ("unchecked_div_signed", Failed),
        // The guard reads like a safe one and is not: `127 + 1` overflows `i8`.
        // The unsigned overflow test would call it safe, which is the bug this
        // case exists to catch.
        ("signed_add_misguarded", Failed),
        // A magnitude bound that holds in both directions.
        ("signed_add_guarded", Verified),
        // A product of two magnitude-10 values, well inside `i8`.
        ("signed_mul_guarded", Verified),
        // Both operands negative, so a zero-extending widening would understate
        // the product and miss the overflow; the sign-extended one sees it.
        ("signed_mul_negative", Failed),
        // Negation guarded against `MIN`, the one input with no positive form.
        ("checked_neg", Verified),

        // --- a guard the programmer wrote -----------------------------------
        // `assert!` and `panic!` lower to a *diverging* call with no return arm.
        // The frontend used to read that as an unmodelled line and drop the path,
        // so the assert was never checked; it is now a panic obligation, and the
        // pair below pins both directions.
        ("assert_guarded", Verified),
        ("assert_misguarded", Failed),
        ("panic_guarded", Verified),
    ]
}

fn main() {
    let only: Vec<String> = expectations().iter().map(|(n, _)| n.to_string()).collect();
    let report = match verify::verify_file(std::path::Path::new(TARGET), &only) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("could not verify: {e}");
            std::process::exit(2);
        }
    };

    println!("=== {TARGET} ===");
    for (name, outcome) in &report.outcomes {
        println!("{name:16} {outcome}");
    }
    if !report.missing.is_empty() {
        println!("\ncontracted but absent from the MIR: {:?}", report.missing);
    }
    println!(
        "\nverified={} failed={} incomplete={}",
        report.verified(),
        report.failed(),
        report.incomplete()
    );

    let mut bad = Vec::new();
    for (name, want) in expectations() {
        let Some((_, outcome)) = report.outcomes.iter().find(|(n, _)| n == name) else {
            bad.push(format!("{name}: not in the report"));
            continue;
        };
        let got = match outcome {
            FnOutcome::Verified { .. } => Expect::Verified,
            FnOutcome::Failed { .. } => Expect::Failed,
            FnOutcome::Incomplete { .. } => Expect::Incomplete,
            FnOutcome::Skipped { .. } => {
                bad.push(format!("{name}: skipped ({outcome})"));
                continue;
            }
        };
        if got != want {
            bad.push(format!("{name}: expected {want:?}, got {got:?} — {outcome}"));
        }
    }

    if bad.is_empty() {
        println!("All expectations met.");
    } else {
        println!("\nUNEXPECTED:");
        for b in &bad {
            println!("  {b}");
        }
        std::process::exit(1);
    }
}
