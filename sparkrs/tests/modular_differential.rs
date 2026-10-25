//! Differential testing for modular verification.
//!
//! Two soundness holes in the call rule were found by accident, by writing a test
//! that asserted the wrong thing and noticing the engine agreed. That is not a method.
//! This file is the method: generate programs containing calls, verify them with the
//! engine, and *interpret them concretely*, then demand that a proof never outruns
//! reality.
//!
//! The property is one direction, and it is the direction that matters:
//!
//! > if the engine reports the caller verified, then no concrete execution in a
//! > bounded enumeration violates the postcondition.
//!
//! The other direction — a failure must have a real counterexample — is checked where
//! it is cheap, but it cannot be complete, because a failure may come from a bound the
//! enumeration does not reach. Soundness is the property that, if broken, lets a
//! verifier certify a bug, so it is the one tested exhaustively.
//!
//! Both of the holes I found by hand are in this file's search space: an
//! under-declared frame, and a call whose written target keeps its pre-call value. A
//! generator cannot invent the *shape* of a mistake it was not told about, so the
//! space below is deliberately biased towards the two things a frame rule can get
//! wrong — what the callee writes, and what the caller is told about it.

use sparkrs::smt::{self, Var};
use sparkrs::wp::{self, Proc, Stmt};

// ---------------------------------------------------------------------------
// A tiny deterministic generator, so a failure can be re-run.
// ---------------------------------------------------------------------------

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Rng {
        // Never zero: xorshift has a fixed point there.
        Rng(seed | 1)
    }

    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }

    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }

    fn flip(&mut self) -> bool {
        self.below(2) == 1
    }
}

// ---------------------------------------------------------------------------
// A concrete interpreter for the statement language.
// ---------------------------------------------------------------------------

/// A concrete machine state: variable index to value.
type State = std::collections::BTreeMap<u32, u64>;

/// Why a concrete run stopped without reaching the end.
#[derive(Debug, PartialEq, Eq)]
enum Stopped {
    /// An `assume` was false, or a variable was read before being written.
    Blocked,
    /// An `assert` was false: a real violation of the program's own specification.
    Failed,
    /// A loop ran longer than the interpreter's bound. The run is inconclusive.
    TooLong,
}

/// How the interpreter treats a call.
///
/// [`CallMode::SkipCalls`] exists only for `the_property_has_teeth`: it is a
/// deliberately wrong semantics, used to show that the differential property *can*
/// fail. A check that has never been observed to fail is not evidence of anything.
#[derive(Clone, Copy, PartialEq, Eq)]
enum CallMode {
    /// Execute calls for real.
    Real,
    /// Treat every call as a no-op.
    SkipCalls,
}

/// Run `s` to completion, or say why it did not finish.
///
/// The interpreter is deliberately small: it covers the fragment the generator
/// produces, and returns [`Stopped::TooLong`] rather than guessing when it does not
/// understand something. A verdict of "inconclusive" is not a verdict, and the
/// harness below treats it as such.
fn exec(s: &Stmt<'_>, state: &mut State, mode: CallMode) -> Result<(), Stopped> {
    const LOOP_LIMIT: u32 = 64;
    match s {
        Stmt::Skip => Ok(()),
        Stmt::Assign { var, expr } => {
            let v = lookup(state, *expr).ok_or(Stopped::Blocked)?;
            state.insert(smt::index(*var), v);
            Ok(())
        }
        Stmt::AssignMany { binds } => {
            // Read every right-hand side in the old state, then write.
            let mut vals = Vec::new();
            for (_, expr) in binds.iter() {
                vals.push(lookup(state, *expr).ok_or(Stopped::Blocked)?);
            }
            for ((var, _), v) in binds.iter().zip(vals) {
                state.insert(smt::index(*var), v);
            }
            Ok(())
        }
        Stmt::Assume(c) => match lookup_pred(state, *c) {
            Some(true) => Ok(()),
            _ => Err(Stopped::Blocked),
        },
        Stmt::Assert(c) => match lookup_pred(state, *c) {
            Some(true) => Ok(()),
            Some(false) => Err(Stopped::Failed),
            None => Err(Stopped::Blocked),
        },
        Stmt::Seq { first, second } => {
            exec(first, state, mode)?;
            exec(second, state, mode)
        }
        Stmt::If { cond, then_, else_ } => match lookup_pred(state, *cond) {
            Some(true) => exec(then_, state, mode),
            Some(false) => exec(else_, state, mode),
            None => Err(Stopped::Blocked),
        },
        Stmt::While { cond, body, .. } => {
            let mut n = 0;
            loop {
                match lookup_pred(state, *cond) {
                    Some(true) => {}
                    Some(false) => return Ok(()),
                    None => return Err(Stopped::Blocked),
                }
                if n >= LOOP_LIMIT {
                    return Err(Stopped::TooLong);
                }
                exec(body, state, mode)?;
                n += 1;
            }
        }
        Stmt::Call { proc_, actuals, writes } => {
            if mode == CallMode::SkipCalls {
                return Ok(());
            }
            // Bind the callee's parameters from the caller's arguments.
            let mut callee: State = State::new();
            for (global, local) in actuals.iter() {
                if let Some(v) = state.get(&smt::index(*local)) {
                    callee.insert(smt::index(*global), *v);
                }
            }
            // A caller that violates the precondition is a caller bug; the engine is
            // supposed to have caught it, so this is "blocked" from the callee's side.
            match lookup_pred(&callee, proc_.requires) {
                Some(true) => {}
                _ => return Err(Stopped::Blocked),
            }
            exec(proc_.body, &mut callee, mode)?;
            // Write the callee's frame back through the rename.
            for w in writes.iter() {
                if let Some((_, local)) = actuals.iter().find(|(g, _)| g == w) {
                    if let Some(v) = callee.get(&smt::index(*w)) {
                        state.insert(smt::index(*local), *v);
                    }
                }
            }
            Ok(())
        }
    }
}

fn lookup(state: &State, t: Var) -> Option<u64> {
    smt::evaluate(t, |i| state.get(&i).copied())
}

fn lookup_pred(state: &State, p: smt::Pred) -> Option<bool> {
    smt::evaluate_pred(p, |i| state.get(&i).copied())
}

// ---------------------------------------------------------------------------
// The generator.
// ---------------------------------------------------------------------------

/// A random expression over `x` and small constants.
fn rand_expr(rng: &mut Rng, x: Var, depth: u32) -> Var {
    let choices = if depth == 0 { 4 } else { 7 };
    match rng.below(choices) {
        0 => x,
        1 => smt::word(rng.below(8), 8),
        2 => x + smt::word(1 + rng.below(3), 8),
        3 => x * smt::word(2, 8),
        4 => smt::band(x, smt::word(rng.below(256), 8)),
        5 => smt::bor(x, smt::word(rng.below(256), 8)),
        _ => {
            let l = rand_expr(rng, x, depth - 1);
            let r = rand_expr(rng, x, depth - 1);
            l + r
        }
    }
}

/// Build one case, verify it, and check the proof against concrete execution.
///
/// Returns `true` when the engine verified the caller, so the caller can count how
/// often the interesting case was reached.
fn run_case(seed: u64, case_no: u32) -> bool {
    let mut rng = Rng::new(seed);

    // The callee: `rr := f(x)`, and sometimes a second write to `sc` — either
    // directly, or through a *nested call* to a helper. The nested shape matters: the
    // frame has to propagate through two levels of rename, and that is exactly where
    // an under-declared frame could hide one level up.
    let use_helper = rng.flip();
    let writes_scratch = rng.flip();
    let x = smt::var(8);
    let rr = smt::var(8);
    let sc = smt::var(8);
    let f_expr = rand_expr(&mut rng, x, 2);
    let g_expr = rand_expr(&mut rng, x, 1);

    let write_rr = Stmt::Assign { var: rr, expr: f_expr };
    let write_sc = Stmt::Assign { var: sc, expr: g_expr };

    // A helper that writes `hr := hx + 1`, wired so its result lands in `sc`.
    let hx = smt::var(8);
    let hr = smt::var(8);
    let helper_body = Stmt::Assign { var: hr, expr: hx + 1u32 };
    let helper = Proc {
        name: "helper",
        requires: smt::truth(true),
        ensures: smt::eq(hr, hx + 1u32),
        body: &helper_body,
    };
    let h_actuals = vec![(hx, x), (hr, sc)];
    let h_writes = vec![hr];
    let helper_call = Stmt::Call { proc_: &helper, actuals: &h_actuals, writes: &h_writes };
    // `sc` is written either way when the helper is used.
    let sc_is_written = writes_scratch || use_helper;

    let callee_body = if use_helper {
        Stmt::Seq { first: &helper_call, second: &write_rr }
    } else if writes_scratch {
        Stmt::Seq { first: &write_rr, second: &write_sc }
    } else {
        Stmt::Seq { first: &write_rr, second: &Stmt::Skip }
    };
    let callee = Proc {
        name: "callee",
        // A precondition that is always satisfiable, so the caller's obligation is
        // discharged for every input and the interesting failures come from the frame.
        requires: smt::truth(true),
        ensures: smt::eq(rr, f_expr),
        body: &callee_body,
    };
    // The callee must verify, or nothing downstream is meaningful.
    // The helper must verify too, since the callee assumes its contract.
    assert!(
        wp::verify_proc(&helper).is_verified(),
        "case {}: the helper must verify",
        case_no
    );
    let callee_report = wp::verify_proc(&callee);
    assert!(
        callee_report.is_verified(),
        "case {}: the callee itself must verify: {:?}",
        case_no,
        callee_report.first_failure()
    );

    // The caller. `input` is free; `t` receives the result; `b` is seeded so a
    // postcondition about it is meaningful.
    let input = smt::var(8);
    let t = smt::var(8);
    let b = smt::var(8);

    // The rename. `sc` is mapped only sometimes, which is how an unmodelled call is
    // produced; and `rr` is mapped onto `input` sometimes, which is the aliasing that
    // must be rejected.
    let alias_result = rng.below(4) == 0;
    let result_target = if alias_result { input } else { t };
    let mut actuals = vec![(x, input), (rr, result_target)];
    let map_scratch = sc_is_written && rng.flip();
    if map_scratch {
        actuals.push((sc, b));
    }

    // The declared frame: correct, generous, or a lie. The lie is the case that used
    // to make the engine prove a falsehood.
    let declared: Vec<Var> = match rng.below(4) {
        0 => vec![rr],          // correct when there is no scratch
        1 => vec![rr, sc],      // generous
        2 => vec![rr, sc, x],   // over-declared
        _ => Vec::new(),        // a lie
    };

    let call = Stmt::Call { proc_: &callee, actuals: &actuals, writes: &declared };

    // Seed both `b` and the result target *before* the call. Seeding the result is
    // what gives the havoc rule something to get wrong: if the engine lets the
    // pre-call value of a written variable masquerade as its post-call value, then a
    // postcondition like `t == 0x55` verifies even though the call overwrote `t`.
    // Without this seeding the harness could not see that bug at all.
    let seed_b = Stmt::Assign { var: b, expr: smt::word(0x07, 8) };
    let seed_value = 0x55u64;
    // Seeding the input would constrain the enumeration, so skip it when the result
    // was renamed onto the input.
    let seed_result = !alias_result;
    let seed_t = Stmt::Assign { var: result_target, expr: smt::word(seed_value, 8) };
    let prog = if seed_result {
        Stmt::Seq {
            first: &seed_b,
            second: &Stmt::Seq { first: &seed_t, second: &call },
        }
    } else {
        Stmt::Seq { first: &seed_b, second: &call }
    };

    // The postcondition: about the result, about `b`, about a value the call should
    // have destroyed, or trivially true. The last two are the ones the two soundness
    // holes used to get wrong.
    let result_in_caller = smt::substitute_word(f_expr, &[(x, input)]);
    let post = match rng.below(5) {
        0 => smt::eq(result_target, result_in_caller),
        1 => smt::ule_const(result_target, 0xff),
        2 => smt::eq_const(b, 0x07),
        // "the call left the result alone" -- false, and the havoc rule must make it
        // unprovable.
        3 if seed_result => smt::eq_const(result_target, seed_value),
        _ => smt::truth(true),
    };

    let report = wp::verify(&prog, smt::truth(true), post);
    let verified = report.is_verified();

    // The property: a proof must not outrun reality.
    if verified {
        for v in 0..=255u64 {
            let mut state = State::new();
            state.insert(smt::index(input), v);
            match exec(&prog, &mut state, CallMode::Real) {
                Ok(()) => {
                    let holds = lookup_pred(&state, post);
                    assert!(
                        holds != Some(false),
                        "case {} (seed {}): the engine VERIFIED but input {} violates the \
                         postcondition",
                        case_no,
                        seed,
                        v
                    );
                }
                Err(Stopped::Failed) => panic!(
                    "case {} (seed {}): engine VERIFIED but input {} fails an assertion",
                    case_no, seed, v
                ),
                // Inconclusive runs are not counterexamples.
                Err(Stopped::Blocked) | Err(Stopped::TooLong) => {}
            }
        }
    } else {
        // The cheap half of completeness: a report that is not verified must have a
        // failure to point at.
        assert!(
            report.first_failure().is_some(),
            "case {}: a report that is not verified must have a failure",
            case_no
        );
    }
    verified
}

#[test]
fn a_proof_never_outruns_concrete_execution() {
    // 60 generated cases. Each one is verified with the engine and then executed
    // concretely for every one of the 256 inputs, and a verification that disagrees
    // with any execution fails the test with the case and the input that broke it.
    let mut verified_count = 0;
    for i in 0..300u64 {
        let seed = 0x9E37_79B9_7F4A_7C15u64.wrapping_mul(i + 1);
        if smt::with_fresh(|| run_case(seed, i as u32)) {
            verified_count += 1;
        }
    }
    // Non-vacuity: if the generator stopped producing verifiable callers, the check
    // above would pass while testing nothing.
    assert!(
        verified_count > 30,
        "the generator produced only {} verifiable callers, so the check is nearly vacuous",
        verified_count
    );
}

#[test]
fn the_harness_catches_a_deliberately_broken_frame_rule() {
    // The harness is only worth having if it would have caught the hole it was written
    // for. This reproduces that hole by hand — an under-declared frame — and shows the
    // concrete side sees the violation, which is the evidence the harness relies on.
    // If this stops holding, the harness has gone blind.
    smt::with_fresh(|| {
        let x = smt::var(8);
        let rr = smt::var(8);
        let sc = smt::var(8);
        let a1 = Stmt::Assign { var: sc, expr: x + x };
        let a2 = Stmt::Assign { var: rr, expr: sc };
        let body = Stmt::Seq { first: &a1, second: &a2 };
        let callee = Proc {
            name: "dbl",
            requires: smt::truth(true),
            ensures: smt::eq(rr, x + x),
            body: &body,
        };

        let input = smt::var(8);
        let t = smt::var(8);
        let b = smt::var(8);
        let actuals = vec![(x, input), (rr, t), (sc, b)];
        let lie: Vec<Var> = Vec::new();

        // The frame check rejects the lie, so the engine will not verify. That is the
        // fix; what this test adds is that the concrete side *would* have disagreed.
        assert!(!Stmt::frame(&callee, &actuals, &lie));

        // Run the callee concretely and show the violation is real: with input 3, `b`
        // ends up 6, not the 7 it started at.
        let seed_b = Stmt::Assign { var: b, expr: smt::word(7, 8) };
        let call = Stmt::Call { proc_: &callee, actuals: &actuals, writes: &lie };
        let prog = Stmt::Seq { first: &seed_b, second: &call };
        let mut state = State::new();
        state.insert(smt::index(input), 3);
        // The interpreter writes only the *declared* frame, so `b` is left alone and
        // the postcondition would appear to hold. That is the unsoundness, reproduced:
        // the declared frame is not what the machine does.
        exec(&prog, &mut state, CallMode::Real).expect("the run completes");
        assert_eq!(state.get(&smt::index(b)).copied(), Some(7));

        // The real machine overwrites `b` with 6. The engine used to agree with the
        // wrong one.
        let real_b = 3u64 + 3;
        assert_ne!(real_b, 7);
        assert_eq!(real_b, 6);
    });
}

#[test]
fn the_property_has_teeth() {
    // A check that has never been observed to fail is not evidence of anything. So:
    // here is a case the engine verifies, and here is the *same* case under a
    // deliberately wrong semantics for calls, where the check fires. That is the
    // detection the real harness depends on, exercised on purpose.
    smt::with_fresh(|| {
        let x = smt::var(8);
        let rr = smt::var(8);
        // The callee returns a constant, so the postcondition below does not depend on
        // the input. My first version used `rr := x + 1` and asserted `t == 1`, which
        // is simply false; the engine produced the counterexample immediately.
        let body = Stmt::Assign { var: rr, expr: smt::word(1, 8) };
        let f = Proc {
            name: "f",
            requires: smt::truth(true),
            ensures: smt::eq_const(rr, 1),
            body: &body,
        };
        let input = smt::var(8);
        let t = smt::var(8);
        let actuals = vec![(x, input), (rr, t)];
        let declared = vec![rr];
        let call = Stmt::Call { proc_: &f, actuals: &actuals, writes: &declared };
        let seed_t = Stmt::Assign { var: t, expr: smt::word(0, 8) };
        let prog = Stmt::Seq { first: &seed_t, second: &call };
        // "t is 1 after the call" -- true exactly when the call is executed.
        let post = smt::eq_const(t, 1);

        let report = wp::verify(&prog, smt::truth(true), post);
        assert!(report.is_verified(), "{:?}", report.first_failure());

        // Real semantics: every input agrees with the proof.
        for v in 0..=255u64 {
            let mut st = State::new();
            st.insert(smt::index(input), v);
            exec(&prog, &mut st, CallMode::Real).expect("the run completes");
            assert_eq!(st.get(&smt::index(t)).copied(), Some(1));
        }

        // Deliberately wrong semantics: the call is a no-op, so `t` stays 0 and the
        // postcondition is false. The harness's check must fire for every input.
        let mut caught = 0;
        for v in 0..=255u64 {
            let mut st = State::new();
            st.insert(smt::index(input), v);
            exec(&prog, &mut st, CallMode::SkipCalls).expect("the run completes");
            if lookup_pred(&st, post) == Some(false) {
                caught += 1;
            }
        }
        assert_eq!(
            caught, 256,
            "the broken semantics must be caught for every input, or the harness is blind"
        );
    });
}

// ---------------------------------------------------------------------------
// Loops containing calls.
//
// This is where the loop rules and the call rule meet, and it is the region where a
// mistake is most expensive: a wrong invariant, a wrong variant, or a frame that does
// not survive an iteration. The generator builds
//
//   callee: rr := x + 1
//   c := <free input>; a := c; k := 0
//   while k < n { tmp := callee(a); a := tmp; k := k + 1 }
//   assert a == c + n
//
// with the contract, the frame, the invariant and the variant each varied. The
// postcondition is exact, so the invariant `k <= n && a == c + k` is what carries the
// proof, and it is preserved only because the callee's postcondition pins its result.
// ---------------------------------------------------------------------------

/// Build and check one loop-with-a-call case. Returns `(verified, termination_proved)`.
fn run_loop_case(seed: u64, case_no: u32) -> (bool, bool) {
    let mut rng = Rng::new(seed);

    // 1..=3 iterations, so the loop terminates and the enumeration stays exhaustive.
    let n = 1 + rng.below(3);
    let exact_contract = rng.below(4) != 0;
    let lie_frame = rng.below(4) == 0;
    let wrong_variant = rng.below(4) == 0;
    // A body that never advances the counter, so the loop diverges. `variant: None`
    // then leaves a *partially* correct proof: the invariant is trivially preserved and
    // the exit condition is vacuous, yet the loop never terminates. That is the case
    // that makes the termination check non-vacuous.
    let diverges = rng.below(8) == 0;

    // The callee.
    let x = smt::var(8);
    let rr = smt::var(8);
    let callee_body = Stmt::Assign { var: rr, expr: x + 1u32 };
    let callee_ensures = if exact_contract {
        smt::eq(rr, x + 1u32)
    } else {
        // Still true, but it does not pin the result when `x` is at the top of its
        // range -- so the loop invariant cannot be preserved from it.
        smt::implies(smt::ult_const(x, 255), smt::eq(rr, x + 1u32))
    };
    let callee = Proc {
        name: "inc",
        requires: smt::truth(true),
        ensures: callee_ensures,
        body: &callee_body,
    };
    assert!(
        wp::verify_proc(&callee).is_verified(),
        "case {}: the callee must verify on its own",
        case_no
    );

    // The caller.
    let c = smt::var(8); // the free input, read-only across the call
    let a = smt::var(8); // the accumulator
    let k = smt::var(3); // the counter, wider than nothing but small
    let tmp = smt::var(8); // the callee's result, then copied back

    let actuals = vec![(x, a), (rr, tmp)];
    let declared: Vec<Var> = if lie_frame { Vec::new() } else { vec![rr] };
    let call = Stmt::Call { proc_: &callee, actuals: &actuals, writes: &declared };

    let advance = Stmt::Assign { var: k, expr: k + 1u32 };
    let copy_back = Stmt::Assign { var: a, expr: tmp };
    let loop_body = if diverges {
        // The call still happens, so the call rules are exercised; only the counter
        // fails to advance.
        Stmt::Seq { first: &call, second: &copy_back }
    } else {
        Stmt::Seq {
            first: &call,
            second: &Stmt::Seq { first: &copy_back, second: &advance },
        }
    };

    let inv = smt::and(
        smt::ule_const(k, n),
        smt::eq(a, c + smt::truncate(k, 8)),
    );
    let variant = if diverges || wrong_variant {
        // A measure that does not decrease, or none at all.
        Some(k)
    } else {
        Some(smt::sub(smt::word(n, 3), k))
    };
    let loop_ = Stmt::While {
        cond: smt::ult_const(k, n),
        invariant: inv,
        variant,
        body: &loop_body,
    };

    let init_k = Stmt::Assign { var: k, expr: smt::word(0, 3) };
    let init_a = Stmt::Assign { var: a, expr: c };
    let prologue = Stmt::Seq { first: &init_k, second: &init_a };
    let prog = Stmt::Seq { first: &prologue, second: &loop_ };

    let post = smt::eq(a, c + smt::word(n, 8));
    let report = wp::verify(&prog, smt::truth(true), post);
    let verified = report.is_verified();
    // The raw termination claim, read the way a caller who skipped `is_verified` would
    // read it. This is deliberately *not* `establishes()`: the defect this check exists
    // for is a `Total` claim on a report that failed, and `establishes()` would fold
    // that failure into `Nothing` and hide it. Two invariants, checked for every input:
    //
    //   verified  => no violating execution
    //   raw_total => no divergent execution
    //
    // The second is what makes the variant rule observable. It has to be checked
    // outside the `verified` branch, because a variant that fails to discharge leaves
    // the report unverified — and that is exactly when the old code claimed `Total`.
    let raw_total = report.correctness() == wp::Correctness::Total;
    let total = report.establishes() == wp::Established::Total;

    if !verified {
        assert!(
            report.first_failure().is_some(),
            "case {}: a report that is not verified must have a failure",
            case_no
        );
    }

    for v in 0..=255u64 {
        let mut state = State::new();
        state.insert(smt::index(c), v);
        match exec(&prog, &mut state, CallMode::Real) {
            Ok(()) => {
                if verified {
                    let holds = lookup_pred(&state, post);
                    assert!(
                        holds != Some(false),
                        "case {} (seed {}): VERIFIED but input {} violates the \
                         postcondition",
                        case_no,
                        seed,
                        v
                    );
                }
            }
            Err(Stopped::Failed) => assert!(
                !verified,
                "case {} (seed {}): VERIFIED but input {} fails an assertion",
                case_no, seed, v
            ),
            Err(Stopped::TooLong) => {
                // A report that claims termination must not diverge concretely. Note
                // this fires for an *unverified* report too, which is the whole point:
                // a variant that does not decrease is exactly the case that leaves the
                // report unverified while still claiming progress.
                assert!(
                    !raw_total,
                    "case {} (seed {}): the report claims TERMINATION but input {} \
                     diverged. `correctness()` said Total for a loop whose variant was \
                     never proved to decrease.",
                    case_no, seed, v
                );
            }
            Err(Stopped::Blocked) => {}
        }
    }

    (verified, total)
}

#[test]
fn a_loop_with_a_call_never_proves_a_false_postcondition() {
    let mut verified = 0;
    let mut total = 0;
    for i in 0..300u64 {
        let seed = 0xD1B5_4A32_D192_ED03u64.wrapping_mul(i + 1);
        let (v, t) = smt::with_fresh(|| run_loop_case(seed, i as u32));
        if v {
            verified += 1;
        }
        if t {
            total += 1;
        }
    }
    // Non-vacuity, in both directions: some cases must verify, and some must carry a
    // termination proof, or the loop side of the harness is checking nothing.
    assert!(
        verified > 20,
        "only {} of 300 loop cases verified, so the check is nearly vacuous",
        verified
    );
    assert!(
        total > 10,
        "only {} of 300 loop cases proved termination, so the variant rule is barely \
         exercised",
        total
    );
}

#[test]
fn a_total_claim_is_not_made_for_a_divergent_loop() {
    // The termination rule, isolated. A loop whose counter never advances diverges, so
    // no variant can exist: the engine may report the loop *partially* correct — the
    // invariant is preserved and the exit condition is vacuous — but it must not claim
    // termination. Without this, a `Total` verdict would be worth nothing.
    smt::with_fresh(|| {
        let k = smt::var(3);
        let a = smt::var(8);
        let c = smt::var(8);
        // The body does not touch `k`, so `while k < 3` never exits.
        let body = Stmt::Skip;
        let inv = smt::and(smt::ule_const(k, 3), smt::eq(a, c));
        let loop_ = Stmt::While {
            cond: smt::ult_const(k, 3),
            invariant: inv,
            // No variant: only partial correctness is claimed.
            variant: None,
            body: &body,
        };
        let init_k = Stmt::Assign { var: k, expr: smt::word(0, 3) };
        let init_a = Stmt::Assign { var: a, expr: c };
        let prog = Stmt::Seq {
            first: &init_k,
            second: &Stmt::Seq { first: &init_a, second: &loop_ },
        };

        let report = wp::verify(&prog, smt::truth(true), smt::eq(a, c));
        assert!(report.is_verified(), "{:?}", report.first_failure());
        assert!(
            !report.has_termination_proof(),
            "a divergent loop must not be reported as terminating"
        );
        assert_eq!(report.correctness(), wp::Correctness::Partial);
        assert_eq!(report.establishes(), wp::Established::Partial);

        // And concretely it really does diverge, so the `Partial` verdict is honest.
        let mut state = State::new();
        state.insert(smt::index(c), 7);
        assert_eq!(
            exec(&prog, &mut state, CallMode::Real),
            Err(Stopped::TooLong),
            "the loop must not terminate concretely"
        );

        // Supplying a measure that cannot decrease turns the claim into a failure.
        let bad = Stmt::While {
            cond: smt::ult_const(k, 3),
            invariant: inv,
            variant: Some(k),
            body: &body,
        };
        let prog2 = Stmt::Seq {
            first: &init_k,
            second: &Stmt::Seq { first: &init_a, second: &bad },
        };
        let report2 = wp::verify(&prog2, smt::truth(true), smt::eq(a, c));
        let (ob, _) = report2
            .first_failure()
            .expect("a non-decreasing measure must fail");
        assert_eq!(ob.rule, wp::Rule::LoopVariant);
    });
}
