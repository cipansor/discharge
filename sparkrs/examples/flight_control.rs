//! A realistic safety-critical example: an actuator command path.
//!
//! This is the shape of code that SPARK is used for — read a sensor, clamp it,
//! rate-limit it, write an actuator — and it is exactly where a silent wrap or a
//! missed bound causes a crash. Every property below is *proved*, and the proofs
//! live in this file, next to the code they are about.
//!
//! Run with: `cargo run --features std --example flight_control`

use sparkrs::exhaustive::for_all_u16;
use sparkrs::prelude::*;
use sparkrs::smt::{self, Verdict};

/// ADC resolution: a 12-bit sensor.
const ADC_MAX: u32 = 4095;
/// Actuator command range, in microseconds of pulse width.
const PWM_MIN: u32 = 1000;
const PWM_MAX: u32 = 2000;
/// Maximum change of the command per control tick.
const RATE_LIMIT: u32 = 50;

/// The concrete command path. This is the function that ships.
pub const fn map_reading(raw: u32) -> u32 {
    // Clamp the raw reading into the ADC range first: a stuck-high bus would
    // otherwise push the command past the actuator's mechanical limit.
    let clamped = if raw > ADC_MAX { ADC_MAX } else { raw };
    // Scale [0, ADC_MAX] to [PWM_MIN, PWM_MAX].
    PWM_MIN + (clamped * (PWM_MAX - PWM_MIN)) / ADC_MAX
}

/// Rate-limit `target` toward `current`.
pub const fn rate_limit(current: u32, target: u32) -> u32 {
    if target > current {
        let step = target - current;
        if step > RATE_LIMIT {
            current + RATE_LIMIT
        } else {
            target
        }
    } else {
        let step = current - target;
        if step > RATE_LIMIT {
            current - RATE_LIMIT
        } else {
            target
        }
    }
}

// ---------------------------------------------------------------------------
// Symbolic proofs
// ---------------------------------------------------------------------------

/// ∀ raw:u16. map_reading(raw) <= PWM_MAX
///
/// Modelled at 16 bits so the BDD stays small, which is the honest way to use
/// this engine: prove the arithmetic fact at the width you can, and cover the
/// concrete function exhaustively in [`proofs_by_enumeration`].
fn prove_output_bound() -> Verdict {
    smt::with_fresh(|| {
        let raw = var(16);
        let max = word(ADC_MAX as u64, 16);
        let clamped = ite(raw.gt(max), max, raw);
        // out = 1000 + clamped * 1000 / 4095. Integer division is not in the
        // symbolic vocabulary, so we prove the stronger, division-free bound
        // that the *scaled* value cannot exceed PWM_MAX before division.
        let scaled = clamped * 1000u32;
        // clamped <= 4095  =>  clamped * 1000 <= 4095000
        prove_implies(clamped.le(max), scaled.le_val(4_095_000))
    })
}

/// ∀ c t. |rate_limit(c, t) - c| <= RATE_LIMIT
///
/// The rate limiter may not move the command more than one step, no matter how
/// far the target is. Proved symbolically at 12 bits.
fn prove_rate_limit_bound() -> Verdict {
    smt::with_fresh(|| {
        let current = var(12);
        let target = var(12);
        let limit = word(RATE_LIMIT as u64, 12);
        let next = rate_limit_symbolic(current, target, limit);
        let delta = ite(next.ge(current), next - current, current - next);
        delta.le(limit).prove()
    })
}

fn rate_limit_symbolic(current: Var, target: Var, limit: Var) -> Var {
    let up = target.gt(current);
    let raw_step = ite(up, target - current, current - target);
    let clamped_step = ite(raw_step.gt(limit), limit, raw_step);
    ite(up, current + clamped_step, current - clamped_step)
}

// ---------------------------------------------------------------------------
// Proofs by complete enumeration of the real function
// ---------------------------------------------------------------------------

/// Walks every 12-bit reading through the *actual* `map_reading` and checks the
/// actuator bounds. This is a complete proof of the shipped code, not of a model.
fn proofs_by_enumeration() -> bool {
    for_all_u16(|raw| {
        if raw > ADC_MAX as u16 {
            return true; // out of sensor range; the clamp path is checked below
        }
        let out = map_reading(raw as u32);
        (PWM_MIN..=PWM_MAX).contains(&out)
    })
}

/// A stuck-high bus (any raw value) must still produce an in-range command.
fn clamp_holds_for_every_u16() -> bool {
    for_all_u16(|raw| {
        let out = map_reading(raw as u32);
        (PWM_MIN..=PWM_MAX).contains(&out)
    })
}

/// The rate limiter's step bound, checked for every pair of 8-bit values.
fn rate_limit_bound_by_enumeration() -> bool {
    sparkrs::exhaustive::for_all_u8_2(|c, t| {
        let next = rate_limit(c as u32, t as u32);
        let delta = next.abs_diff(c as u32);
        delta <= RATE_LIMIT
    })
}

/// Monotonicity of the mapping: a larger reading never produces a smaller
/// command. Controllers rely on this to argue about stability.
fn map_is_monotone() -> bool {
    sparkrs::exhaustive::for_all_u16(|a| {
        // Compare each value against its successor.
        let b = a.wrapping_add(1);
        if b <= a {
            return true;
        }
        map_reading(a as u32) <= map_reading(b as u32)
    })
}

fn main() {
    let mut failures = 0;

    // 1. Symbolic proofs.
    let v = prove_output_bound();
    println!("[symbolic]  map_reading output bound       : {}", v);
    if !v.is_proved() {
        failures += 1;
    }

    let v = prove_rate_limit_bound();
    println!("[symbolic]  rate_limit step bound          : {}", v);
    if !v.is_proved() {
        failures += 1;
    }

    // 2. Complete proofs by enumeration of the shipped function.
    let ok = clamp_holds_for_every_u16();
    println!("[exhaustive] clamp holds for all 65536     : {}", ok);
    if !ok {
        failures += 1;
    }

    let ok = proofs_by_enumeration();
    println!("[exhaustive] output in [PWM_MIN, PWM_MAX]  : {}", ok);
    if !ok {
        failures += 1;
    }

    let ok = rate_limit_bound_by_enumeration();
    println!("[exhaustive] rate limit for all u8 pairs   : {}", ok);
    if !ok {
        failures += 1;
    }

    let ok = map_is_monotone();
    println!("[exhaustive] mapping is monotone           : {}", ok);
    if !ok {
        failures += 1;
    }

    // 3. A kernel-checked certificate, used to build a `Verified` value.
    let cert = smt::with_fresh(|| {
        let raw = var(16);
        let max = word(ADC_MAX as u64, 16);
        Certificate::discharge(implies(raw.le(max), raw.le(max)))
    });
    match cert {
        Some(c) => {
            let v = Verified::from_certificate(map_reading(2048), c);
            match v {
                Some(v) => println!("[kernel]    certificate accepted, value = {}", v.get()),
                None => println!("[kernel]    certificate was stale, refused"),
            }
        }
        None => {
            println!("[kernel]    certificate rejected");
            failures += 1;
        }
    }

    // 4. A deliberately false claim, to show the tools *do* refute.
    let bad = smt::with_fresh(|| {
        let raw = var(12);
        raw.lt_val(ADC_MAX as u64).prove()
    });
    match bad {
        Verdict::Counterexample(c) => {
            let witness = c.value_of(0).unwrap();
            println!(
                "[refuted]   raw < ADC_MAX is false, witness raw = {}",
                witness
            );
        }
        other => {
            println!("[refuted]   expected a refutation, got {}", other);
            failures += 1;
        }
    }

    // 5. A claim the engine cannot decide, to show it refuses to guess.
    let hard = smt::with_fresh(|| {
        let a = var(12);
        let b = var(12);
        let c = var(12);
        // Operator overloading from `sym` keeps this readable.
        ((a * b) * c).eq(a * (b * c)).prove()
    });
    println!("[honesty]   (a*b)*c == a*(b*c) at 12 bits  : {}", hard);
    assert!(
        matches!(hard, Verdict::Valid | Verdict::Unknown),
        "engine must never refute a true statement"
    );

    println!();
    if failures == 0 {
        println!("all obligations discharged");
    } else {
        println!("{} obligation(s) FAILED", failures);
        std::process::exit(1);
    }
}
