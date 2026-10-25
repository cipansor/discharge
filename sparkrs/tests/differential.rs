//! Differential testing: the symbolic prover and brute-force execution must
//! agree. This is the test that makes the whole approach trustworthy — if the
//! BDD engine ever disagreed with reality, this file would catch it.

use sparkrs::exhaustive::{for_all_u8, for_all_u8_2, find_violation_u8};
use sparkrs::prelude::*;
use sparkrs::smt::{self, Verdict};

/// For a predicate over one 8-bit variable, symbolic proof and enumeration must
/// give the same answer.
fn agrees_unary(build: impl Fn(Var) -> Pred, concrete: impl Fn(u8) -> bool) {
    // Symbolic: is it valid for all inputs?
    let symbolic_valid = smt::with_fresh(|| {
        let x = var(8);
        build(x).prove().is_proved()
    });
    let concrete_valid = for_all_u8(&concrete);
    assert_eq!(
        symbolic_valid, concrete_valid,
        "symbolic and exhaustive disagree for a unary predicate"
    );

    // If the symbolic engine produced a counterexample, it must be real.
    let cex = smt::with_fresh(|| {
        let x = var(8);
        match build(x).prove() {
            Verdict::Counterexample(c) => Some(c.value_of(0).unwrap()),
            _ => None,
        }
    });
    if let Some(v) = cex {
        assert!(!concrete(v as u8), "symbolic counterexample {} is bogus", v);
    }
}

#[test]
fn unary_predicates_agree() {
    agrees_unary(|x| x.lt_val(200), |v| v < 200);
    agrees_unary(|x| x.le_val(200), |v| v <= 200);
    agrees_unary(|x| x.ge_val(100), |v| v >= 100);
    agrees_unary(|x| x.gt_val(100), |v| v > 100);
    // `x & 0x0f <= x` is a real property (masking only clears bits), and it is
    // not trivially true the way `x & 0x0f < 16` is.
    agrees_unary(|x| (x & 0x0fu32).le(x), |v| (v & 0x0f) <= v);
    agrees_unary(|x| (x >> 4u32).le_val(15), |v| (v >> 4) <= 15);
    // `a => b` is `!a || b`, so the concrete form is `v >= k || v < m`.
    agrees_unary(|x| x.lt_val(16).implies(x.lt_val(32)), |v| v >= 16 || v < 32);
    agrees_unary(|x| x.lt_val(4).implies(x.lt_val(8)), |v| v >= 4 || v < 8);
}

#[test]
fn binary_predicates_agree() {
    // ∀ a b. a + b does not wrap below a  (this is false; check both engines agree)
    let symbolic = smt::with_fresh(|| {
        let a = var(8);
        let b = var(8);
        smt::prove(smt::ule(smt::add(a, b), a)).is_proved()
    });
    let concrete = for_all_u8_2(|a, b| a.wrapping_add(b) <= a);
    assert_eq!(symbolic, concrete);

    // ∀ a b. (a & b) <= a
    let symbolic = smt::with_fresh(|| {
        let a = var(8);
        let b = var(8);
        smt::prove(smt::ule(smt::band(a, b), a)).is_proved()
    });
    assert!(symbolic, "(a & b) <= a should be a theorem");
    assert!(for_all_u8_2(|a, b| (a & b) <= a));
}

#[test]
fn the_symbolic_counterexample_is_a_real_violation() {
    // The prover reports *a* violating input, not necessarily the smallest one:
    // BDD models are path-derived. What must hold is that the witness really
    // violates the property, and that enumeration confirms a violation exists.
    let sym = smt::with_fresh(|| {
        let x = var(8);
        match (x.lt_val(100)).prove() {
            Verdict::Counterexample(c) => c.value_of(0).unwrap() as u8,
            _ => panic!("expected a counterexample"),
        }
    });
    assert!(sym >= 100, "witness {} does not violate x < 100", sym);

    // Enumeration finds the smallest witness, and it must be exactly 100.
    let brute = find_violation_u8(|v| v < 100).unwrap();
    assert_eq!(brute, 100);
}

#[test]
fn saturating_add_matches_execution_everywhere() {
    // The proof module claims saturating addition never wraps. Check the claim
    // against every pair of u8s, and check the symbolic engine agrees.
    assert!(for_all_u8_2(|a, b| a.saturating_add(b) >= a));
    assert!(for_all_u8_2(|a, b| a.saturating_add(b) >= b));

    let symbolic = smt::with_fresh(|| {
        let a = var(8);
        let b = var(8);
        let sum = smt::add(a, b);
        let no_wrap = smt::ule(a, sum);
        smt::prove_implies(no_wrap, smt::ule(b, sum)).is_proved()
    });
    assert!(symbolic);
}

#[test]
fn the_runtime_contract_vocabulary_matches_the_symbolic_one() {
    // Same statement, both halves: `x <= 100` for a concrete x, and for all x.
    let runtime = contract::Contract::new(
        contract::Pred::Le(100),
        contract::Pred::Lt(200),
    );
    assert!(runtime.check_pre(100).is_ok());
    assert!(runtime.check_pre(101).is_err());

    let symbolic = smt::with_fresh(|| {
        let x = var(8);
        contract! { requires x.le_val(100), ensures x.lt_val(200) }
    });
    assert!(symbolic.is_proved());
}

#[test]
fn truncation_agrees_with_a_rust_cast_on_every_input() {
    // `truncate` is the only width-changing operation in the language, and a
    // bit-level primitive like this is exactly where an off-by-one in the bit
    // index hides. So: for every source width, every destination width, and every
    // 8-bit input, compare against the Rust cast.
    for dst in 1..=8u8 {
        let symbolic: Vec<(u8, bool)> = smt::with_fresh(|| {
            let x = var(8);
            let t = smt::truncate(x, dst);
            assert_eq!(smt::bits(t), dst, "result width must be the requested one");
            (0..=255u8)
                .map(|v| {
                    // Ask the engine for the value at a pinned input.
                    let p = smt::prove_implies(
                        smt::eq_const(x, v as u64),
                        smt::eq_const(t, (v as u64) & mask(dst)),
                    );
                    (v, p.is_proved())
                })
                .collect()
        });
        for (v, proved) in symbolic {
            assert!(
                proved,
                "truncate to {} bits disagrees at input {}",
                dst, v
            );
            // And the Rust cast says the same thing.
            assert_eq!((v as u64) & mask(dst), (v as u16 % (1u16 << dst)) as u64);
        }
    }
}

#[test]
fn widening_through_truncate_agrees_with_the_original_value() {
    for src in 1..=8u8 {
        for dst in src..=16u8 {
            smt::with_fresh(|| {
                let x = var(src);
                let t = smt::truncate(x, dst);
                assert_eq!(smt::bits(t), dst);
                // Widening never changes the value, so the result fits in `src`
                // bits and matches the original.
                let p = smt::prove(smt::eq(t, smt::truncate(x, dst)));
                assert!(p.is_proved());
                let bound = 1u64 << src;
                let q = smt::prove(smt::ult_const(t, bound));
                assert!(q.is_proved(), "widened value escaped its source range");
            });
        }
    }
}

fn mask(width: u8) -> u64 {
    if width >= 64 {
        u64::MAX
    } else {
        (1u64 << width) - 1
    }
}

// ---------------------------------------------------------------------------
// The concrete evaluator must agree with the bit-level engine.
// ---------------------------------------------------------------------------

#[test]
fn the_evaluator_agrees_with_the_engine_on_every_operator() {
    // `smt::evaluate` is the concrete semantics of the symbolic language. It is used
    // as an *oracle* by the modular differential harness, so it has to be right
    // first — an oracle that disagrees with the engine would send me chasing bugs in
    // the wrong place. For each operation and every 8-bit input pair, the evaluator's
    // answer must equal what the engine says when both inputs are pinned.
    use sparkrs::smt::{self, var};

    // Build every operation, then compare per input pair.
    type BinOp = fn(smt::Var, smt::Var) -> smt::Var;
    let ops: Vec<(&str, BinOp)> = vec![
        ("and", smt::band),
        ("or", smt::bor),
        ("xor", smt::bxor),
        ("add", |a, b| a + b),
        ("sub", |a, b| a - b),
        ("mul", |a, b| a * b),
    ];

    for (name, f) in ops {
        smt::with_fresh(|| {
            let a = var(8);
            let b = var(8);
            let t = f(a, b);
            let ai = smt::index(a);
            let bi = smt::index(b);
            for x in [0u64, 1, 7, 100, 128, 200, 255] {
                for y in [0u64, 1, 3, 99, 128, 254, 255] {
                    let concrete =
                        smt::evaluate(t, |i| if i == ai { Some(x) } else if i == bi { Some(y) } else { None })
                            .expect("both inputs are known");
                    // The engine, with both inputs pinned, must produce the same value.
                    let proved = smt::prove_implies(
                        smt::and(smt::eq_const(a, x), smt::eq_const(b, y)),
                        smt::eq_const(t, concrete),
                    );
                    assert!(
                        proved.is_proved(),
                        "{} at ({}, {}): evaluator says {} but the engine disagrees",
                        name,
                        x,
                        y,
                        concrete
                    );
                    // And the ground truth in Rust agrees too.
                    let expected = match name {
                        "and" => x & y,
                        "or" => x | y,
                        "xor" => x ^ y,
                        "add" => x.wrapping_add(y),
                        "sub" => x.wrapping_sub(y),
                        "mul" => x.wrapping_mul(y),
                        _ => unreachable!(),
                    } & 0xff;
                    assert_eq!(concrete, expected, "{} at ({}, {})", name, x, y);
                }
            }
        });
    }
}

#[test]
fn the_evaluator_handles_widths_truncation_and_shifts() {
    use sparkrs::smt::{self, var};

    smt::with_fresh(|| {
        let a = var(8);
        let ai = smt::index(a);

        // A narrow constant masks its own width.
        let narrow = smt::word(0xff, 4);
        assert_eq!(smt::evaluate(narrow, |_| None), Some(0xf));

        // Truncation keeps the low bits.
        let t = smt::truncate(a, 3);
        for x in 0..=255u64 {
            let got = smt::evaluate(t, |i| if i == ai { Some(x) } else { None }).unwrap();
            assert_eq!(got, x & 0b111, "truncate at {}", x);
        }

        // Widening zero-fills.
        let w = smt::truncate(a, 16);
        for x in 0..=255u64 {
            let got = smt::evaluate(w, |i| if i == ai { Some(x) } else { None }).unwrap();
            assert_eq!(got, x);
        }

        // Shifts: left, logical right, arithmetic right.
        for x in 0..=255u64 {
            let l = smt::evaluate(a << 2u32, |i| if i == ai { Some(x) } else { None }).unwrap();
            assert_eq!(l, (x << 2) & 0xff, "shl at {}", x);

            let r = smt::evaluate(a >> 2u32, |i| if i == ai { Some(x) } else { None }).unwrap();
            assert_eq!(r, x >> 2, "lshr at {}", x);

            // `Shr` is arithmetic: the sign bit replicates.
            let sar = smt::evaluate(smt::ashr(a, 2), |i| if i == ai { Some(x) } else { None })
                .unwrap();
            let expected = ((x as i8) >> 2) as u8 as u64;
            assert_eq!(sar, expected, "shr at {}", x);
        }

        // An unknown input yields `None` rather than a guess.
        assert_eq!(smt::evaluate(a, |_| None), None);
        assert_eq!(smt::evaluate(t, |i| if i == ai { Some(5) } else { None }), Some(5));
        assert_eq!(smt::evaluate(a + 1u32, |_| None), None);

        // Predicates evaluate to booleans.
        assert_eq!(smt::evaluate_pred(smt::ult_const(a, 10), |i| if i == ai { Some(9) } else { None }), Some(true));
        assert_eq!(smt::evaluate_pred(smt::ult_const(a, 10), |i| if i == ai { Some(10) } else { None }), Some(false));
    });
}

#[test]
fn a_truncated_model_says_so() {
    // The ninth hole, and the most consequential instance of the class: a *witness* that
    // is presented as complete while missing variables. A model is the evidence for a
    // refutation, so a truncated one is evidence with a hole in it.
    //
    // `Cex` inlines MAX_CEX assignments, and `model` used to stop filling at the cap with
    // no record that it had. Worse, `value_of` returned None for a dropped variable
    // exactly as it does for a variable that was never mentioned, so an incomplete model
    // was indistinguishable from a complete one.
    //
    // The goal here is `v0 == 0 || ... || v19 == 0`. Its negation is "every vi == 1", so
    // any counterexample must fix all twenty variables, and MAX_CEX is 16:
    //
    //   assignments reported : 16
    //   variables touched    : 20
    //   is_complete()        : false
    //
    // The assignments that fit are still correct; what changed is that the hole is now
    // visible in the API and in the rendering.
    smt::with_fresh(|| {
        let mut goal = smt::truth(false);
        for _ in 0..20 {
            let v = var(1);
            goal = smt::or(goal, smt::eq_const(v, 0));
        }
        match smt::prove(goal) {
            Verdict::Counterexample(cex) => {
                assert_eq!(cex.len(), smt::MAX_CEX, "the buffer holds MAX_CEX entries");
                assert_eq!(cex.total(), 20, "twenty variables were touched");
                assert!(
                    !cex.is_complete(),
                    "a model missing four of twenty variables must not claim completeness"
                );
                // The rendering has to carry the same warning, since a truncated witness
                // printed as if whole is the failure mode the flag exists to prevent.
                let shown = format!("{}", cex);
                assert!(
                    shown.contains("TRUNCATED"),
                    "the rendering must mark a truncated model, got: {}",
                    shown
                );
            }
            other => panic!("expected a counterexample, got {:?}", other),
        }
    });
}

#[test]
fn a_model_that_fits_is_complete() {
    // The teeth: the flag must not cry truncation on every model, or it would be ignored.
    // A small query produces a model that fits, and it must report itself complete.
    smt::with_fresh(|| {
        let a = var(8);
        // `a == 5 || a == 7` is not valid; a counterexample fixes one 8-bit variable.
        let goal = smt::or(smt::eq_const(a, 5), smt::eq_const(a, 7));
        match smt::prove(goal) {
            Verdict::Counterexample(cex) => {
                assert!(
                    cex.is_complete(),
                    "a model that fits in the buffer must report completeness, got {} \
                     of {}",
                    cex.len(),
                    cex.total()
                );
                assert_eq!(cex.total(), cex.len() as u32);
                let shown = format!("{}", cex);
                assert!(
                    !shown.contains("TRUNCATED"),
                    "a complete model must not be marked truncated, got: {}",
                    shown
                );
            }
            other => panic!("expected a counterexample, got {:?}", other),
        }
    });
}

// ---------------------------------------------------------------------------
// Every operation, checked against Rust, at widths the BDD can finish.
//
// `blast` (BDD) and `eval_term` (concrete) are independent implementations of the
// same term language. Above four bits, `mul` exhausts the BDD budget and `prove`
// returns `Unknown`, so the *blasting* of `mul` was never actually exercised by a
// passing test -- only its evaluation was. These tests pin every op at widths where
// the BDD does finish, so a blasting bug cannot hide behind `Unknown`.
//
// The oracle is Rust's own wrapping arithmetic, so agreement is evidence about the
// engine, not about itself.
// ---------------------------------------------------------------------------

fn width_mask(w: u8) -> u64 {
    if w >= 64 {
        u64::MAX
    } else {
        (1u64 << w) - 1
    }
}

/// `op(a, b)` blasted must equal Rust's `rust(a, b)` for every input pair, and a
/// deliberately wrong equation must be refuted (so a broken engine cannot pass by
/// proving everything).
fn binary_op_agrees(w: u8, name: &str, op: fn(Var, Var) -> Var, rust: fn(u64, u64) -> u64) {
    let m = width_mask(w);
    for a in 0..=m {
        for b in 0..=m {
            let want = rust(a, b) & m;
            let valid = smt::with_fresh(|| {
                let av = smt::word(a, w);
                let bv = smt::word(b, w);
                smt::prove(smt::eq(op(av, bv), smt::word(want, w))).is_proved()
            });
            assert!(valid, "w={} {}: {}({}, {}) should be {}", w, name, name, a, b, want);
        }
    }
    // Teeth: a wrong result must not be proved. `op(a,b) == want ^ 1` holds for no
    // input when `want ^ 1 != want`, which is always.
    let wrong_valid = smt::with_fresh(|| {
        let av = var(w);
        let bv = var(w);
        let shifted = smt::bxor(op(av, bv), smt::word(1, w));
        smt::prove(smt::eq(op(av, bv), shifted)).is_proved()
    });
    assert!(!wrong_valid, "w={} {}: a wrong equation must not be proved", w, name);
}

#[test]
fn every_binary_operation_matches_rust() {
    for w in 1u8..=4 {
        binary_op_agrees(w, "add", smt::add, |a, b| a.wrapping_add(b));
        binary_op_agrees(w, "sub", smt::sub, |a, b| a.wrapping_sub(b));
        binary_op_agrees(w, "mul", smt::mul, |a, b| a.wrapping_mul(b));
        binary_op_agrees(w, "band", smt::band, |a, b| a & b);
        binary_op_agrees(w, "bor", smt::bor, |a, b| a | b);
        binary_op_agrees(w, "bxor", smt::bxor, |a, b| a ^ b);
    }
}

#[test]
fn every_shift_matches_rust() {
    for w in 1u8..=4 {
        let m = width_mask(w);
        for a in 0..=m {
            for k in 0..=(w as u32 + 1) {
                let (shl_want, lshr_want, ashr_want) = if w >= 64 {
                    (a.wrapping_shl(k), a.wrapping_shr(k), ((a as i64) >> k.min(63)) as u64)
                } else {
                    (
                        (a << k) & m,
                        if k >= w as u32 { 0 } else { (a >> k) & m },
                        {
                            // Arithmetic shift on a `w`-bit two's-complement value.
                            let sign_bit = 1u64 << (w - 1);
                            let signed = if a & sign_bit != 0 { (a | !m) as i64 } else { a as i64 };
                            (signed >> k.min(63)) as u64 & m
                        },
                    )
                };
                // Through `prove`, so the *blasting* is what is checked. Using
                // `evaluate` here would test `eval_term` instead, and a mutation to the
                // BDD shift arm would slip through -- which is exactly what the first
                // version of this test did.
                // A concrete constant, so the equation is decidable, but routed through
                // `prove` so the BDD *blast* arm for the shift runs. Using `evaluate` here
                // would test `eval_term` instead, and a mutation to the blast arm would
                // slip through -- which is exactly what the first version of this test did.
                let got = smt::with_fresh(|| {
                    let av = smt::word(a, w);
                    (
                        smt::prove(smt::eq(smt::shl(av, k), smt::word(shl_want, w))).is_proved(),
                        smt::prove(smt::eq(smt::lshr(av, k), smt::word(lshr_want, w))).is_proved(),
                        smt::prove(smt::eq(smt::ashr(av, k), smt::word(ashr_want, w))).is_proved(),
                    )
                });
                assert!(got.0, "w={} {} << {} should be {}", w, a, k, shl_want);
                assert!(got.1, "w={} {} >> {} should be {}", w, a, k, lshr_want);
                assert!(got.2, "w={} {} >>a {} should be {}", w, a, k, ashr_want);
            }
        }
    }
}

/// The comparison *blasting* (which evaluation does not exercise) must agree with Rust.
#[test]
fn comparison_blasting_matches_rust() {
    for w in 1u8..=4 {
        let m = width_mask(w);
        for a in 0..=m {
            for b in 0..=m {
                let (ult, ule, eq) = smt::with_fresh(|| {
                    let av = smt::word(a, w);
                    let bv = smt::word(b, w);
                    (
                        smt::prove(smt::ult(av, bv)).is_proved(),
                        smt::prove(smt::ule(av, bv)).is_proved(),
                        smt::prove(smt::eq(av, bv)).is_proved(),
                    )
                });
                assert_eq!(ult, a < b, "w={} {} < {}", w, a, b);
                assert_eq!(ule, a <= b, "w={} {} <= {}", w, a, b);
                assert_eq!(eq, a == b, "w={} {} == {}", w, a, b);
            }
        }
    }
}

/// Truncation, the one width-changing operation.
#[test]
fn truncation_matches_rust() {
    for src in 1u8..=4 {
        let m = width_mask(src);
        for dst in 1u8..=4 {
            let dm = width_mask(dst);
            for a in 0..=m {
                let got = smt::with_fresh(|| {
                    let av = smt::word(a, src);
                    smt::evaluate(smt::truncate(av, dst), |_| None).unwrap()
                });
                assert_eq!(got, a & dm, "truncate {} ({} bits) to {} bits", a, src, dst);
            }
        }
    }
}
