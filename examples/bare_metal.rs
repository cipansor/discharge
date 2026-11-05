//! The prover, compiled for bare metal and built by a *qualified* toolchain.
//!
//! Every other example in this directory needs `std`: they print, they use the
//! thread-local arena, they run on the host. This one is the opposite — it is
//! `#![no_std]`, it has no `main`, and its whole purpose is to be **compiled and
//! linked for `thumbv7em-none-eabihf` with Ferrocene**, the qualified toolchain.
//!
//! That is the claim this crate actually makes, checked the one way it can be
//! checked without shipping to silicon: the decision procedure is not a host-side
//! tool that inspects the artifact, it *is* code in the artifact, so it has to
//! compile and link for the same target the flight software does, on the same
//! qualified compiler. `scripts/gate.sh` gate 3 and the `ferrocene` CI job build
//! exactly this.
//!
//! It is a `crate-type = ["lib"]` example (see `[[example]]` in `Cargo.toml`),
//! because a bare-metal target has no `main` to give it. What matters is that
//! the three functions below are reachable, so the arena, the BDD blasting and
//! the SAT fallback are all monomorphised and codegen'd for the target rather
//! than being dead weight the linker drops.
//!
//! Two halves, each checked where it can be:
//!
//! - **the bare-metal build** is the evidence that the qualified compiler
//!   accepts the engine for the target — a successful `cargo build` for
//!   `thumbv7em-none-eabihf` under Ferrocene;
//! - **the host tests at the bottom** are the evidence that the *answers* are
//!   right, since the target has no test harness. They run under
//!   `cargo test --features std --example bare_metal`.

#![no_std]

use discharge::smt::{self, var, word, Verdict};

/// The command limit an actuator path is built around.
pub const MAX_COMMAND: u16 = 3000;

/// The rate limit on a single step, in the same units as the command.
pub const STEP_LIMIT: u16 = 64;

/// The obligation an actuator path depends on, decided by the embedded engine.
///
/// This is the shape of thing a `Pre`/`Post` pair carries in SPARK: the command
/// is clamped to [`MAX_COMMAND`] and rate-limited to [`STEP_LIMIT`] per step,
/// and the proof obligation is that the result respects both. It is decided
/// here with no solver process, no allocator, and no host.
///
/// It returns a [`Verdict`] rather than asserting, because a bare-metal build has
/// no panic machinery by default: the caller decides what a refuted obligation
/// means, which is the posture the rest of the crate takes.
pub fn verify_actuator_chain() -> Verdict {
    let raw = var(16);
    let prev = var(16);

    // 1. Clamping is idempotent: a value already within the limit is unchanged
    //    by the clamp. A `Pre`/`Post` pair would state exactly this.
    let limit = word(u64::from(MAX_COMMAND), 16);
    let clamped = smt::ite(smt::ule(raw, limit), raw, limit);
    let idempotent = smt::prove_implies(
        smt::ule(raw, limit),
        smt::eq(smt::ite(smt::ule(clamped, limit), clamped, limit), raw),
    );
    if !idempotent.is_proved() {
        return idempotent;
    }

    // 2. The rate limit bounds the *step*, not the value. `delta` is a wrapping
    //    subtraction, which is where a missed bound would hide, and the claim is
    //    that the limited step never exceeds the limit.
    let delta = smt::sub(raw, prev);
    let step = word(u64::from(STEP_LIMIT), 16);
    let limited = smt::ite(smt::ult(delta, step), delta, step);
    smt::prove(smt::ule(limited, step))
}

/// A second obligation, deliberately *false*, so the harness can show that a
/// refuted claim is refuted on the target too rather than the engine being
/// trivially optimistic.
pub fn verify_refuted_claim() -> Verdict {
    let raw = var(16);
    // `raw + 1 <= raw` is false at `raw = u16::MAX`. The wrap is exactly the bug
    // the actuator comment above warns about, so the engine must find it.
    smt::prove(smt::ule(smt::add(raw, word(1, 16)), raw))
}

/// A third obligation that the engine must *refuse* rather than guess at.
///
/// A wide multiplier is where this decision procedure stops: the BDD wall is
/// real, and the crate's stated posture is that `Unknown` is a first-class,
/// safe answer. Returning it here is the behavior being checked, not a failure.
pub fn verify_beyond_the_wall() -> Verdict {
    let a = var(64);
    let b = var(64);
    smt::prove(smt::eq(smt::mul(a, b), smt::mul(b, a)))
}

#[cfg(all(test, feature = "std"))]
mod tests {
    use super::*;

    #[test]
    fn the_actuator_chain_is_proved() {
        // The same function the bare-metal build compiles, decided here so the
        // *verdict* is checked somewhere even though the target has no harness.
        let v = verify_actuator_chain();
        assert!(
            v.is_proved(),
            "the clamp/rate-limit obligation must be proved, got {v:?}"
        );
    }

    #[test]
    fn the_refuted_claim_is_refuted_not_silently_proved() {
        // Teeth: if the engine said `Valid` to everything, this would pass too.
        let v = verify_refuted_claim();
        assert!(
            matches!(v, Verdict::Counterexample(_)),
            "a false claim about wrapping must be refuted, got {v:?}"
        );
    }

    #[test]
    fn a_wide_multiplier_is_refused_rather_than_guessed() {
        // `Unknown` is not a proof and not a refutation; the crate refuses to
        // pretend otherwise. If a future change makes this `Valid`, that is a
        // change to the stated budget and worth noticing here.
        assert!(
            !verify_beyond_the_wall().is_proved(),
            "a 64x64 multiplier must not be reported as proved"
        );
    }
}
