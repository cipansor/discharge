//! Differential testing: the symbolic prover and brute-force execution must
//! agree. This is the test that makes the whole approach trustworthy — if the
//! BDD engine ever disagreed with reality, this file would catch it.

use discharge::exhaustive::{for_all_u8, for_all_u8_2, find_violation_u8};
use discharge::prelude::*;
use discharge::smtscript::Query;
use discharge::smt::{self, Verdict};
use discharge::wp;

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
                // Widening never changes the value, so narrowing the result back to `src`
                // bits must return the original `x`. This was `eq(t, truncate(x, dst))`,
                // which compares `t` with itself -- `t` *is* `truncate(x, dst)` -- so it was
                // a tautology that could not fail, under a comment claiming it checked
                // "matches the original". The round trip through the opposite width is the
                // non-trivial form of the same claim, and it is well sorted because both
                // sides are `src` bits.
                let p = smt::prove(smt::eq(smt::truncate(t, src), x));
                assert!(p.is_proved(), "widening lost the original value");
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
    use discharge::smt::{self, var};

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
    use discharge::smt::{self, var};

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

// ---------------------------------------------------------------------------
// Differential fuzzing: random expression trees, BDD `prove` vs enumeration.
//
// The harnesses above check the shapes I thought of. This checks shapes I did not:
// random trees over two 8-bit variables, compared against enumeration over all 65 536
// inputs. A disagreement in the `Valid` direction, or a witness that does not violate,
// would be unsoundness. The seed is fixed, so a failure is reproducible.
//
// This is the harness that caught a *test-side* error rather than an engine one: Rust's
// `wrapping_shl` masks the shift count by the width (`x << 8` on a `u8` is `x`), while
// this crate's documented semantics is that a shift by at least the width yields zero.
// The oracle was wrong and the engine was right. That divergence is exactly what a
// differential test is for, and it is why the shift semantics is spelled out here.
// ---------------------------------------------------------------------------

struct FuzzLcg(u64);
impl FuzzLcg {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0 >> 33
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

enum FuzzExpr {
    A,
    B,
    K(u8),
    Add(Box<FuzzExpr>, Box<FuzzExpr>),
    Sub(Box<FuzzExpr>, Box<FuzzExpr>),
    Mul(Box<FuzzExpr>, Box<FuzzExpr>),
    And(Box<FuzzExpr>, Box<FuzzExpr>),
    Or(Box<FuzzExpr>, Box<FuzzExpr>),
    Xor(Box<FuzzExpr>, Box<FuzzExpr>),
    Shl(Box<FuzzExpr>, u32),
    Shr(Box<FuzzExpr>, u32),
    Not(Box<FuzzExpr>),
    Trunc(Box<FuzzExpr>, u8),
    /// `ite(c, t, e)`. The condition is a predicate, so the random *word* tree cannot
    /// produce it on its own -- the generator reaches into the predicate grammar for it.
    /// `Trunc` and `Ite` are also the two nodes that hold a *payload* rather than a term id
    /// (the source width and the condition), and the substitution walk has a special case
    /// for each, so generating them makes those cases load-bearing.
    Ite(Box<PFuzz>, Box<FuzzExpr>, Box<FuzzExpr>),
}

impl FuzzExpr {
    fn build(&self, a: Var, b: Var) -> Var {
        match self {
            FuzzExpr::A => a,
            FuzzExpr::B => b,
            FuzzExpr::K(k) => smt::word(*k as u64, 8),
            FuzzExpr::Add(x, y) => smt::add(x.build(a, b), y.build(a, b)),
            FuzzExpr::Sub(x, y) => smt::sub(x.build(a, b), y.build(a, b)),
            FuzzExpr::Mul(x, y) => smt::mul(x.build(a, b), y.build(a, b)),
            FuzzExpr::And(x, y) => smt::band(x.build(a, b), y.build(a, b)),
            FuzzExpr::Or(x, y) => smt::bor(x.build(a, b), y.build(a, b)),
            FuzzExpr::Xor(x, y) => smt::bxor(x.build(a, b), y.build(a, b)),
            FuzzExpr::Shl(x, k) => smt::shl(x.build(a, b), *k),
            FuzzExpr::Shr(x, k) => smt::lshr(x.build(a, b), *k),
            FuzzExpr::Not(x) => smt::bxor(x.build(a, b), smt::word(255, 8)),
            FuzzExpr::Trunc(x, w) => smt::truncate(x.build(a, b), *w),
            FuzzExpr::Ite(c, t, e) => smt::ite(c.build(a, b), t.build(a, b), e.build(a, b)),
        }
    }

    fn eval(&self, a: u8, b: u8) -> u8 {
        match self {
            FuzzExpr::A => a,
            FuzzExpr::B => b,
            FuzzExpr::K(k) => *k,
            FuzzExpr::Add(x, y) => x.eval(a, b).wrapping_add(y.eval(a, b)),
            FuzzExpr::Sub(x, y) => x.eval(a, b).wrapping_sub(y.eval(a, b)),
            FuzzExpr::Mul(x, y) => x.eval(a, b).wrapping_mul(y.eval(a, b)),
            FuzzExpr::And(x, y) => x.eval(a, b) & y.eval(a, b),
            FuzzExpr::Or(x, y) => x.eval(a, b) | y.eval(a, b),
            FuzzExpr::Xor(x, y) => x.eval(a, b) ^ y.eval(a, b),
            // The crate zeroes on an over-wide shift; Rust's `<<` would mask instead.
            FuzzExpr::Shl(x, k) => if *k >= 8 { 0 } else { x.eval(a, b) << k },
            FuzzExpr::Shr(x, k) => if *k >= 8 { 0 } else { x.eval(a, b) >> k },
            FuzzExpr::Not(x) => !x.eval(a, b),
            FuzzExpr::Trunc(x, w) => if *w >= 8 { x.eval(a, b) } else { x.eval(a, b) & ((1u8 << w) - 1) },
            FuzzExpr::Ite(c, t, e) => if c.eval(a, b) { t.eval(a, b) } else { e.eval(a, b) },
        }
    }

    fn render(&self) -> String {
        match self {
            FuzzExpr::A => "a".into(),
            FuzzExpr::B => "b".into(),
            FuzzExpr::K(k) => format!("{}", k),
            FuzzExpr::Add(x, y) => format!("({}+{})", x.render(), y.render()),
            FuzzExpr::Sub(x, y) => format!("({}-{})", x.render(), y.render()),
            FuzzExpr::Mul(x, y) => format!("({}*{})", x.render(), y.render()),
            FuzzExpr::And(x, y) => format!("({}&{})", x.render(), y.render()),
            FuzzExpr::Or(x, y) => format!("({}|{})", x.render(), y.render()),
            FuzzExpr::Xor(x, y) => format!("({}^{})", x.render(), y.render()),
            FuzzExpr::Shl(x, k) => format!("({}<<{})", x.render(), k),
            FuzzExpr::Shr(x, k) => format!("({}>>{})", x.render(), k),
            FuzzExpr::Not(x) => format!("(!{})", x.render()),
            FuzzExpr::Trunc(x, w) => format!("trunc{}({})", w, x.render()),
            FuzzExpr::Ite(c, t, e) => format!("({} ? {} : {})", c.render(), t.render(), e.render()),
        }
    }
}

fn fuzz_expr(r: &mut FuzzLcg, depth: u32) -> FuzzExpr {
    fuzz_expr_maybe_trunc(r, depth, true)
}

/// A width-preserving 8-bit expression: like [`fuzz_expr`] but never `truncate`.
///
/// The predicate layer compares two word expressions, and a comparison across different
/// widths is ill-formed -- the engine refuses the query with `Unknown`. The predicate fuzz
/// wants well-typed terms so that a `Valid`/`Unsat`/counterexample verdict is always
/// meaningful, and the same applies to the exporter and the wp differential, which evaluate
/// the term against a concrete one. The refusal path is exercised elsewhere: by the word
/// fuzz (which only requires "never a wrong `Valid`") and by the dedicated
/// `a_mixed_width_sum_is_refused_not_truncated`.
fn fuzz_expr_w8(r: &mut FuzzLcg, depth: u32) -> FuzzExpr {
    fuzz_expr_maybe_trunc(r, depth, false)
}

fn fuzz_expr_maybe_trunc(r: &mut FuzzLcg, depth: u32, allow_trunc: bool) -> FuzzExpr {
    if depth == 0 || r.below(4) == 0 {
        return match r.below(3) {
            0 => FuzzExpr::A,
            1 => FuzzExpr::B,
            _ => FuzzExpr::K(r.below(256) as u8),
        };
    }
    let choice = r.below(if allow_trunc { 11 } else { 10 });
    let x = fuzz_expr_maybe_trunc(r, depth - 1, allow_trunc);
    let y = fuzz_expr_maybe_trunc(r, depth - 1, allow_trunc);
    match choice {
        0 => FuzzExpr::Add(Box::new(x), Box::new(y)),
        1 => FuzzExpr::Sub(Box::new(x), Box::new(y)),
        2 => FuzzExpr::Mul(Box::new(x), Box::new(y)),
        3 => FuzzExpr::And(Box::new(x), Box::new(y)),
        4 => FuzzExpr::Or(Box::new(x), Box::new(y)),
        5 => FuzzExpr::Xor(Box::new(x), Box::new(y)),
        6 => FuzzExpr::Shl(Box::new(x), r.below(9) as u32),
        7 => FuzzExpr::Shr(Box::new(x), r.below(9) as u32),
        8 => FuzzExpr::Not(Box::new(x)),
        9 if allow_trunc => FuzzExpr::Trunc(Box::new(x), 1 + r.below(8) as u8),
        _ => FuzzExpr::Ite(Box::new(pfuzz_pred(r, depth - 1)), Box::new(x), Box::new(y)),
    }
}

#[test]
fn random_expressions_agree_with_enumeration() {
    let mut r = FuzzLcg(0x1234_5678_9abc_def0);
    let mut decided = 0u32;
    for _ in 0..600 {
        let lhs = fuzz_expr(&mut r, 3);
        let rhs = fuzz_expr(&mut r, 3);
        let concrete_valid = for_all_u8_2(|a, b| lhs.eval(a, b) == rhs.eval(a, b));
        let concrete_ever = !for_all_u8_2(|a, b| lhs.eval(a, b) != rhs.eval(a, b));

        let (verdict, witness) = smt::with_fresh(|| {
            let a = var(8);
            let b = var(8);
            let v = smt::prove(smt::eq(lhs.build(a, b), rhs.build(a, b)));
            let w = match v {
                Verdict::Counterexample(c) => Some((c.value_of(0), c.value_of(1))),
                _ => None,
            };
            (v, w)
        });

        match verdict {
            Verdict::Unknown => {}
            Verdict::Valid => {
                decided += 1;
                assert!(
                    concrete_valid,
                    "claimed Valid but `{} == {}` has a violation",
                    lhs.render(),
                    rhs.render()
                );
            }
            Verdict::Unsat => {
                decided += 1;
                assert!(
                    !concrete_ever,
                    "claimed Unsat but `{} == {}` is satisfiable",
                    lhs.render(),
                    rhs.render()
                );
            }
            Verdict::Counterexample(_) => {
                decided += 1;
                assert!(
                    !concrete_valid,
                    "claimed a counterexample but `{} == {}` is valid",
                    lhs.render(),
                    rhs.render()
                );
                let (ca, cb) = witness.unwrap();
                let (ca, cb) = (ca.unwrap_or(0) as u8, cb.unwrap_or(0) as u8);
                assert_ne!(
                    lhs.eval(ca, cb),
                    rhs.eval(ca, cb),
                    "witness a={} b={} does not violate `{} == {}`",
                    ca,
                    cb,
                    lhs.render(),
                    rhs.render()
                );
            }
        }
    }
    assert!(decided > 200, "too few cases were decided to be meaningful: {}", decided);
}

// ---------------------------------------------------------------------------
// Mixed-width operations must be refused, not truncated.
//
// A bit-vector operation has no natural width when its operands disagree. The engine used
// to take the *left* operand's width and truncate the right one silently. Fuzzing the
// predicate layer found the consequence: `trunc2(b) + (a + 115)` was computed in 2 bits, so
// the right-hand sum was masked to `y & 3`, the sum came out 2 instead of 142, and a
// predicate that is false at (a, b) = (27, 144) read as `Valid`. That is a proof of a false
// statement.
//
// The crate has no widening operation, so the honest answer is to refuse the term. The
// verdict becomes `Unknown` -- never a wrong `Valid`.
// ---------------------------------------------------------------------------

#[test]
fn a_mixed_width_sum_is_refused_not_truncated() {
    let verdict = smt::with_fresh(|| {
        let a = var(8);
        let b = var(8);
        let narrow = smt::truncate(b, 2);
        let wide = smt::add(a, smt::word(115, 8));
        let sum = smt::add(narrow, wide);
        smt::prove(smt::eq(sum, sum))
    });
    assert!(
        matches!(verdict, Verdict::Unknown),
        "a mixed-width sum must be refused, got {}",
        verdict
    );
}

#[test]
fn a_mixed_width_comparison_is_refused() {
    let verdict = smt::with_fresh(|| {
        let a = var(8);
        let b = var(2);
        smt::prove(smt::ult(a, b))
    });
    assert!(
        matches!(verdict, Verdict::Unknown),
        "a mixed-width comparison must be refused, got {}",
        verdict
    );
}

#[test]
fn mixed_width_ite_branches_are_refused() {
    let verdict = smt::with_fresh(|| {
        let c = smt::ult_const(var(8), 3);
        let t = var(8);
        let e = var(2);
        let _ = smt::ite(c, t, e);
        smt::prove(smt::eq(t, t))
    });
    assert!(
        matches!(verdict, Verdict::Unknown),
        "mixed-width ite branches must be refused, got {}",
        verdict
    );
}

#[test]
fn same_width_operations_still_decide() {
    // The teeth on the other side: refusing must not become refusing everything.
    let valid = smt::with_fresh(|| {
        let a = var(8);
        let b = var(8);
        smt::prove(smt::eq(smt::add(a, b), smt::add(b, a))).is_proved()
    });
    assert!(valid, "same-width addition commutativity should still prove");

    let refuted = smt::with_fresh(|| {
        let a = var(8);
        smt::prove(smt::eq(a, smt::add(a, smt::word(1, 8))))
    });
    assert!(
        !refuted.is_proved(),
        "a false same-width equation must not be proved"
    );
}

// ---------------------------------------------------------------------------
// The predicate layer, fuzzed against enumeration.
//
// A wrong boolean connective is the most damaging kind of bug: it turns a refutable
// obligation into a proof. This builds random predicates -- comparisons over random word
// expressions, combined with and/or/not/implies -- proves them symbolically, and compares
// against enumeration over all 65 536 inputs. This is the harness that found the mixed-width
// truncation: it reported `Valid` for a predicate that is false at (a, b) = (27, 144).
// ---------------------------------------------------------------------------

enum PFuzz {
    T,
    F,
    Eq(FuzzExpr, FuzzExpr),
    Lt(FuzzExpr, FuzzExpr),
    Le(FuzzExpr, FuzzExpr),
    Not(Box<PFuzz>),
    And(Box<PFuzz>, Box<PFuzz>),
    Or(Box<PFuzz>, Box<PFuzz>),
    Implies(Box<PFuzz>, Box<PFuzz>),
}

impl PFuzz {
    fn build(&self, a: Var, b: Var) -> Pred {
        match self {
            PFuzz::T => smt::truth(true),
            PFuzz::F => smt::truth(false),
            PFuzz::Eq(x, y) => smt::eq(x.build(a, b), y.build(a, b)),
            PFuzz::Lt(x, y) => smt::ult(x.build(a, b), y.build(a, b)),
            PFuzz::Le(x, y) => smt::ule(x.build(a, b), y.build(a, b)),
            PFuzz::Not(x) => smt::not(x.build(a, b)),
            PFuzz::And(x, y) => smt::and(x.build(a, b), y.build(a, b)),
            PFuzz::Or(x, y) => smt::or(x.build(a, b), y.build(a, b)),
            PFuzz::Implies(x, y) => smt::implies(x.build(a, b), y.build(a, b)),
        }
    }

    fn eval(&self, a: u8, b: u8) -> bool {
        match self {
            PFuzz::T => true,
            PFuzz::F => false,
            PFuzz::Eq(x, y) => x.eval(a, b) == y.eval(a, b),
            PFuzz::Lt(x, y) => x.eval(a, b) < y.eval(a, b),
            PFuzz::Le(x, y) => x.eval(a, b) <= y.eval(a, b),
            PFuzz::Not(x) => !x.eval(a, b),
            PFuzz::And(x, y) => x.eval(a, b) && y.eval(a, b),
            PFuzz::Or(x, y) => x.eval(a, b) || y.eval(a, b),
            PFuzz::Implies(x, y) => !x.eval(a, b) || y.eval(a, b),
        }
    }

    fn render(&self) -> String {
        match self {
            PFuzz::T => "T".into(),
            PFuzz::F => "F".into(),
            PFuzz::Eq(x, y) => format!("({} == {})", x.render(), y.render()),
            PFuzz::Lt(x, y) => format!("({} < {})", x.render(), y.render()),
            PFuzz::Le(x, y) => format!("({} <= {})", x.render(), y.render()),
            PFuzz::Not(x) => format!("!{}", x.render()),
            PFuzz::And(x, y) => format!("({} && {})", x.render(), y.render()),
            PFuzz::Or(x, y) => format!("({} || {})", x.render(), y.render()),
            PFuzz::Implies(x, y) => format!("({} => {})", x.render(), y.render()),
        }
    }
}

fn pfuzz_pred(r: &mut FuzzLcg, depth: u32) -> PFuzz {
    if depth == 0 || r.below(4) == 0 {
        // The comparison operands use the *same* depth this call received. They used to be
        // generated at a fixed depth of 2, which is fine only while a word tree cannot reach
        // back into the predicate grammar. Once `ite` did, `pfuzz_pred(1)` -> `fuzz_expr(2)`
        // -> `pfuzz_pred(1)` was a cycle that never decremented and overflowed the stack.
        // Threading the depth through makes the pair terminate: `fuzz_expr(d)` reaches
        // `pfuzz_pred(d - 1)`, and the base here reaches `fuzz_expr(d)`, so each round trip
        // loses one level.
        return match r.below(5) {
            0 => PFuzz::T,
            1 => PFuzz::F,
            2 => PFuzz::Eq(fuzz_expr_w8(r, depth), fuzz_expr_w8(r, depth)),
            3 => PFuzz::Lt(fuzz_expr_w8(r, depth), fuzz_expr_w8(r, depth)),
            _ => PFuzz::Le(fuzz_expr_w8(r, depth), fuzz_expr_w8(r, depth)),
        };
    }
    let choice = r.below(4);
    let x = pfuzz_pred(r, depth - 1);
    let y = pfuzz_pred(r, depth - 1);
    match choice {
        0 => PFuzz::Not(Box::new(x)),
        1 => PFuzz::And(Box::new(x), Box::new(y)),
        2 => PFuzz::Or(Box::new(x), Box::new(y)),
        _ => PFuzz::Implies(Box::new(x), Box::new(y)),
    }
}

#[test]
fn random_predicates_agree_with_enumeration() {
    let mut r = FuzzLcg(0x0bad_c0de_dead_beef);
    let mut decided = 0u32;
    for _ in 0..300 {
        let p = pfuzz_pred(&mut r, 3);
        let concrete_valid = for_all_u8_2(|a, b| p.eval(a, b));

        let (verdict, witness) = smt::with_fresh(|| {
            let a = var(8);
            let b = var(8);
            let v = smt::prove(p.build(a, b));
            let w = match v {
                Verdict::Counterexample(c) => Some((c.value_of(0), c.value_of(1))),
                _ => None,
            };
            (v, w)
        });

        match verdict {
            Verdict::Unknown => {}
            Verdict::Valid => {
                decided += 1;
                assert!(concrete_valid, "claimed Valid but `{}` has a violation", p.render());
            }
            Verdict::Unsat => {
                decided += 1;
                assert!(!concrete_valid, "claimed Unsat but `{}` holds for every input", p.render());
            }
            Verdict::Counterexample(_) => {
                decided += 1;
                assert!(!concrete_valid, "claimed a counterexample but `{}` is valid", p.render());
                let (ca, cb) = witness.unwrap();
                let (ca, cb) = (ca.unwrap_or(0) as u8, cb.unwrap_or(0) as u8);
                assert!(
                    !p.eval(ca, cb),
                    "witness a={} b={} does not falsify `{}`",
                    ca,
                    cb,
                    p.render()
                );
            }
        }
    }
    assert!(decided > 50, "too few predicates were decided: {}", decided);
}

// ---------------------------------------------------------------------------
// The weakest-precondition transformer, checked against a concrete interpreter.
//
// The tests above check the *decision procedure* against enumeration. This one checks the
// thing that runs before it: `wp(post, program)` rewrites the postcondition through the
// assignments that dominate it, and if that rewriting is wrong the prover will faithfully
// prove the wrong statement. So for random straight-line and branching programs, evaluate
// the generated `wp` at every one of the 256 inputs and compare against running the same
// program concretely. Exhaustive, and it does not depend on the BDD engine at all.
// ---------------------------------------------------------------------------

enum WpStep {
    Assign(FuzzExpr),
    If(PFuzz, Vec<WpStep>, Vec<WpStep>),
}

fn build_wp_steps(steps: &[WpStep], acc: Var, x: Var) -> &'static Stmt<'static> {
    let mut seq = Stmt::Skip;
    for s in steps.iter().rev() {
        let one = match s {
            WpStep::Assign(e) => Stmt::Assign { var: acc, expr: e.build(acc, x) },
            WpStep::If(c, t, e) => Stmt::If {
                cond: c.build(acc, x),
                then_: build_wp_steps(t, acc, x),
                else_: build_wp_steps(e, acc, x),
            },
        };
        seq = Stmt::Seq {
            first: Box::leak(Box::new(one)),
            second: Box::leak(Box::new(seq)),
        };
    }
    Box::leak(Box::new(seq))
}

fn run_wp_steps(steps: &[WpStep], mut acc: u8, x: u8) -> u8 {
    for s in steps {
        match s {
            WpStep::Assign(e) => acc = e.eval(acc, x),
            WpStep::If(c, t, e) => {
                acc = if c.eval(acc, x) {
                    run_wp_steps(t, acc, x)
                } else {
                    run_wp_steps(e, acc, x)
                };
            }
        }
    }
    acc
}

fn render_wp_steps(steps: &[WpStep], out: &mut String) {
    out.push('[');
    for s in steps {
        match s {
            WpStep::Assign(e) => out.push_str(&format!("acc := {}; ", e.render())),
            WpStep::If(c, t, e) => {
                out.push_str(&format!("if {} {{ ", c.render()));
                render_wp_steps(t, out);
                out.push_str("} else { ");
                render_wp_steps(e, out);
                out.push_str("} ");
            }
        }
    }
    out.push(']');
}

fn gen_wp_steps(r: &mut FuzzLcg, depth: u32, n: usize) -> Vec<WpStep> {
    (0..n)
        .map(|_| {
            if depth > 0 && r.below(3) == 0 {
                let (nt, ne) = (r.below(3) as usize, r.below(3) as usize);
                let t = gen_wp_steps(r, depth - 1, nt);
                let e = gen_wp_steps(r, depth - 1, ne);
                WpStep::If(pfuzz_pred(r, 2), t, e)
            } else {
                WpStep::Assign(fuzz_expr_w8(r, 2))
            }
        })
        .collect()
}

#[test]
fn wp_matches_concrete_execution() {
    let mut r = FuzzLcg(0x51ee_d00d_1234_5678);
    for _ in 0..250 {
        let n = 1 + r.below(4) as usize;
        let steps = gen_wp_steps(&mut r, 2, n);
        let post = pfuzz_pred(&mut r, 2);

        smt::with_fresh(|| {
            let x = var(8);
            let acc = var(8);
            // `acc := x; <steps>`: acc is always defined, so the postcondition never
            // mentions a free `acc`.
            let prog = build_wp_steps(&steps, acc, x);
            let post_p = post.build(acc, x);
            let w = wp::wp(post_p, prog);

            let (ia, ix) = (acc.index(), x.index());
            for v in 0..=255u8 {
                // `acc` starts at `x`; both name the same input.
                let env = |i: u32| {
                    if i == ix || i == ia {
                        Some(v as u64)
                    } else {
                        None
                    }
                };
                let got = smt::evaluate_pred(w, env);
                let want = post.eval(run_wp_steps(&steps, v, v), v);
                if got != Some(want) {
                    let mut prog_s = String::new();
                    render_wp_steps(&steps, &mut prog_s);
                    panic!(
                        "wp(post, program) disagrees with concrete execution at x={}\n  program: {}\n  post: {}\n  got {:?} want {:?}",
                        v,
                        prog_s,
                        post.render(),
                        got,
                        Some(want)
                    );
                }
            }
        });
    }
}

// ---------------------------------------------------------------------------
// Substitution must not walk a shift amount as if it were a term id.
//
// A shift node stores its amount in the `b` field, which every other binary node uses for
// a term id. `subst` walked `b` regardless, so substituting through `x << 3` recursed into
// whatever term happened to have id 3. When that term contained the shift itself the
// recursion never bottomed out -- `wp` on a two-line program blew the stack. When it did
// not, the walk still touched an unrelated term, so a stale or oversized id there could
// flip the `stale` flag and turn a provable goal into `Unknown`.
// ---------------------------------------------------------------------------

#[test]
fn substitution_through_a_shift_is_finite_and_correct() {
    smt::with_fresh(|| {
        let x = var(8);
        let y = var(8);
        // `x << 3` then substitute `x := y`. The shift amount (3) must survive untouched.
        let shifted = smt::shl(x, 3);
        let sub = smt::substitute_word(shifted, &[(x, y)]);
        assert_eq!(smt::bits(sub), 8);
        let y_idx = y.index();
        let x_idx = x.index();
        for v in 0..=255u8 {
            let got = smt::evaluate(sub, |i| if i == y_idx { Some(v as u64) } else { None });
            let want = (v as u64) << 3 & 0xff;
            assert_eq!(got, Some(want), "x<<3 with x={} substituted to y should be {}", v, want);
        }

        // And the same through the weakest-precondition transformer, which is where the
        // crash showed up.
        let prog = Stmt::Assign { var: x, expr: smt::shl(x, 3) };
        let w = wp::wp(smt::ult_const(x, 200), &prog);
        for v in 0..=255u8 {
            let got = smt::evaluate_pred(w, |i| if i == x_idx { Some(v as u64) } else { None });
            let want = (v as u64) << 3 & 0xff < 200;
            assert_eq!(got, Some(want), "wp through a shift disagrees at x={}", v);
        }
    });
}

// ---------------------------------------------------------------------------
// The SMT-LIB2 export, checked by an independent parser.
//
// `smtscript.rs` turns a verification condition into SMT-LIB2 so an external solver can
// reproduce the proof. That makes the printer soundness-critical: if it prints a different
// formula, or an ill-sorted one, the external evidence does not apply. Three bugs were found
// here by reading the output (inverted polarity, `bvnot` on a boolean, `extract` for a
// widening truncate). Reading is not a check, so this is the check: a small independent
// reader that (a) rejects any ill-sorted operator application and (b) evaluates the parsed
// text, which is then compared against the predicate it came from, over all 65 536 inputs.
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, PartialEq, Eq)]
enum Sort {
    Bool,
    Bv(u8),
}

#[derive(Debug, Clone)]
enum E {
    BoolConst(bool),
    BvConst(u64, u8),
    Var(u32, u8),
    Not(Box<E>),
    And(Box<E>, Box<E>),
    Or(Box<E>, Box<E>),
    Xor(Box<E>, Box<E>),
    BvNot(Box<E>),
    BvAnd(Box<E>, Box<E>),
    BvOr(Box<E>, Box<E>),
    BvXor(Box<E>, Box<E>),
    BvAdd(Box<E>, Box<E>),
    BvSub(Box<E>, Box<E>),
    BvMul(Box<E>, Box<E>),
    BvShl(Box<E>, Box<E>),
    BvLShr(Box<E>, Box<E>),
    BvAshr(Box<E>, Box<E>),
    Eq(Box<E>, Box<E>),
    BvUlt(Box<E>, Box<E>),
    BvUle(Box<E>, Box<E>),
    Extract(u8, u8, Box<E>),
    ZeroExtend(u8, Box<E>),
    Ite(Box<E>, Box<E>, Box<E>),
}

fn bit_mask(w: u8) -> u64 {
    if w >= 64 {
        u64::MAX
    } else {
        (1u64 << w) - 1
    }
}

impl E {
    fn sort(&self) -> Sort {
        match self {
            E::BoolConst(_) | E::Not(_) | E::And(..) | E::Or(..) | E::Xor(..) | E::Eq(..)
            | E::BvUlt(..) | E::BvUle(..) => Sort::Bool,
            E::BvConst(_, w) => Sort::Bv(*w),
            E::Var(_, w) => Sort::Bv(*w),
            E::BvNot(x) => x.sort(),
            E::BvAnd(a, _)
            | E::BvOr(a, _)
            | E::BvXor(a, _)
            | E::BvAdd(a, _)
            | E::BvSub(a, _)
            | E::BvMul(a, _)
            | E::BvShl(a, _)
            | E::BvLShr(a, _)
            | E::BvAshr(a, _) => a.sort(),
            E::Extract(hi, lo, _) => Sort::Bv(hi - lo + 1),
            E::ZeroExtend(n, x) => match x.sort() {
                Sort::Bv(w) => Sort::Bv(w + n),
                Sort::Bool => Sort::Bool,
            },
            E::Ite(_, t, _) => t.sort(),
        }
    }

    fn eval(&self, a: u64, b: u64) -> V {
        match self {
            E::BoolConst(v) => V::B(*v),
            E::BvConst(v, w) => V::W(*v, *w),
            E::Var(idx, w) => V::W(if *idx == 0 { a } else { b }, *w),
            E::Not(x) => V::B(!x.eval(a, b).b()),
            E::And(x, y) => V::B(x.eval(a, b).b() && y.eval(a, b).b()),
            E::Or(x, y) => V::B(x.eval(a, b).b() || y.eval(a, b).b()),
            E::Xor(x, y) => V::B(x.eval(a, b).b() ^ y.eval(a, b).b()),
            E::BvNot(x) => {
                let (v, w) = x.eval(a, b).w();
                V::W(!v & bit_mask(w), w)
            }
            E::BvAnd(x, y) => {
                let (v, w) = x.eval(a, b).w();
                V::W(v & y.eval(a, b).w().0, w)
            }
            E::BvOr(x, y) => {
                let (v, w) = x.eval(a, b).w();
                V::W(v | y.eval(a, b).w().0, w)
            }
            E::BvXor(x, y) => {
                let (v, w) = x.eval(a, b).w();
                V::W(v ^ y.eval(a, b).w().0, w)
            }
            E::BvAdd(x, y) => {
                let (v, w) = x.eval(a, b).w();
                V::W(v.wrapping_add(y.eval(a, b).w().0) & bit_mask(w), w)
            }
            E::BvSub(x, y) => {
                let (v, w) = x.eval(a, b).w();
                V::W(v.wrapping_sub(y.eval(a, b).w().0) & bit_mask(w), w)
            }
            E::BvMul(x, y) => {
                let (v, w) = x.eval(a, b).w();
                V::W(v.wrapping_mul(y.eval(a, b).w().0) & bit_mask(w), w)
            }
            E::BvShl(x, y) => {
                let (v, w) = x.eval(a, b).w();
                let sh = y.eval(a, b).w().0;
                V::W(if sh >= w as u64 { 0 } else { (v << sh) & bit_mask(w) }, w)
            }
            E::BvLShr(x, y) => {
                let (v, w) = x.eval(a, b).w();
                let sh = y.eval(a, b).w().0;
                V::W(if sh >= w as u64 { 0 } else { v >> sh }, w)
            }
            E::BvAshr(x, y) => {
                let (v, w) = x.eval(a, b).w();
                let sh = y.eval(a, b).w().0;
                let sign = (v >> (w - 1)) & 1 == 1;
                let r = if sh >= w as u64 {
                    if sign {
                        bit_mask(w)
                    } else {
                        0
                    }
                } else if sign {
                    (v >> sh) | !(bit_mask(w) >> sh)
                } else {
                    v >> sh
                };
                V::W(r & bit_mask(w), w)
            }
            E::Eq(x, y) => V::B(x.eval(a, b).w().0 == y.eval(a, b).w().0),
            E::BvUlt(x, y) => V::B(x.eval(a, b).w().0 < y.eval(a, b).w().0),
            E::BvUle(x, y) => V::B(x.eval(a, b).w().0 <= y.eval(a, b).w().0),
            E::Extract(hi, lo, x) => {
                let (v, _) = x.eval(a, b).w();
                let width = hi - lo + 1;
                V::W((v >> lo) & bit_mask(width), width)
            }
            E::ZeroExtend(n, x) => {
                let (v, w) = x.eval(a, b).w();
                V::W(v, w + n)
            }
            E::Ite(c, t, e) => {
                if c.eval(a, b).b() {
                    t.eval(a, b)
                } else {
                    e.eval(a, b)
                }
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
enum V {
    B(bool),
    W(u64, u8),
}

impl V {
    fn b(self) -> bool {
        match self {
            V::B(v) => v,
            V::W(v, _) => v != 0,
        }
    }
    fn w(self) -> (u64, u8) {
        match self {
            V::W(v, w) => (v & bit_mask(w), w),
            V::B(v) => (u64::from(v), 1),
        }
    }
}

struct Reader<'a> {
    s: &'a [u8],
    i: usize,
}

impl<'a> Reader<'a> {
    fn new(s: &'a str) -> Self {
        Reader {
            s: s.as_bytes(),
            i: 0,
        }
    }

    fn skip_ws(&mut self) {
        while self.i < self.s.len() && self.s[self.i].is_ascii_whitespace() {
            self.i += 1;
        }
    }

    fn token(&mut self) -> Result<String, String> {
        self.skip_ws();
        let start = self.i;
        while self.i < self.s.len()
            && !self.s[self.i].is_ascii_whitespace()
            && self.s[self.i] != b'('
            && self.s[self.i] != b')'
        {
            self.i += 1;
        }
        if start == self.i {
            return Err(format!("expected a token at byte {}", self.i));
        }
        Ok(String::from_utf8_lossy(&self.s[start..self.i]).into_owned())
    }

    fn eat(&mut self, c: u8) -> Result<(), String> {
        self.skip_ws();
        if self.i < self.s.len() && self.s[self.i] == c {
            self.i += 1;
            Ok(())
        } else {
            Err(format!("expected '{}' at byte {}", c as char, self.i))
        }
    }

    fn peek(&mut self) -> Option<u8> {
        self.skip_ws();
        self.s.get(self.i).copied()
    }

    fn width_of(&self, name: &str) -> Result<u8, String> {
        let rest = name
            .strip_prefix('x')
            .ok_or_else(|| format!("unknown symbol {}", name))?;
        let (_idx, w) = rest
            .split_once('_')
            .ok_or_else(|| format!("bad symbol {}", name))?;
        w.parse::<u8>().map_err(|_| format!("bad width in {}", name))
    }

    fn index_of(&self, name: &str) -> Result<u32, String> {
        let rest = name
            .strip_prefix('x')
            .ok_or_else(|| format!("unknown symbol {}", name))?;
        let (idx, _w) = rest
            .split_once('_')
            .ok_or_else(|| format!("bad symbol {}", name))?;
        idx.parse::<u32>()
            .map_err(|_| format!("bad index in {}", name))
    }

    fn term(&mut self) -> Result<E, String> {
        self.skip_ws();
        if self.peek() == Some(b'(') {
            return self.list();
        }
        let t = self.token()?;
        match t.as_str() {
            "true" => Ok(E::BoolConst(true)),
            "false" => Ok(E::BoolConst(false)),
            _ => {
                let w = self.width_of(&t)?;
                let idx = self.index_of(&t)?;
                Ok(E::Var(idx, w))
            }
        }
    }

    fn list(&mut self) -> Result<E, String> {
        self.eat(b'(')?;
        // An *indexed application* is `((_ extract 7 0) x)`: two opening parentheses,
        // because the operator itself is a parenthesised `(_ ...)` head. Only the
        // self-contained literal `(_ bvN w)` has a single `(`. This branch was missing, so
        // the reader rejected every well-formed `extract`/`zero_extend` -- and the
        // "rejects what the old exporter printed" test then passed for the wrong reason, by
        // failing to parse rather than by sort-checking.
        if self.peek() == Some(b'(') {
            self.eat(b'(')?;
            return self.indexed();
        }
        if self.peek() == Some(b'_') {
            return self.indexed();
        }
        let head = self.token()?;
        let out = match head.as_str() {
            "not" => E::Not(Box::new(self.bool_arg()?)),
            "and" => {
                let a = self.bool_arg()?;
                let b = self.bool_arg()?;
                E::And(Box::new(a), Box::new(b))
            }
            "or" => {
                let a = self.bool_arg()?;
                let b = self.bool_arg()?;
                E::Or(Box::new(a), Box::new(b))
            }
            "xor" => {
                let a = self.bool_arg()?;
                let b = self.bool_arg()?;
                E::Xor(Box::new(a), Box::new(b))
            }
            "distinct" => {
                let a = self.term()?;
                let b = self.term()?;
                if a.sort() != b.sort() {
                    return Err("distinct on different sorts".into());
                }
                if b.eval(0, 0).w().0 != 0 {
                    return Err("distinct with a nonzero constant".into());
                }
                E::Not(Box::new(E::Eq(
                    Box::new(a),
                    Box::new(E::BvConst(0, b.eval(0, 0).w().1)),
                )))
            }
            "bvnot" => E::BvNot(Box::new(self.bv_arg()?)),
            "bvand" => {
                let a = self.bv_arg()?;
                let b = self.bv_arg()?;
                same_width(&a, &b, "bvand")?;
                E::BvAnd(Box::new(a), Box::new(b))
            }
            "bvor" => {
                let a = self.bv_arg()?;
                let b = self.bv_arg()?;
                same_width(&a, &b, "bvor")?;
                E::BvOr(Box::new(a), Box::new(b))
            }
            "bvxor" => {
                let a = self.bv_arg()?;
                let b = self.bv_arg()?;
                same_width(&a, &b, "bvxor")?;
                E::BvXor(Box::new(a), Box::new(b))
            }
            "bvadd" => {
                let a = self.bv_arg()?;
                let b = self.bv_arg()?;
                same_width(&a, &b, "bvadd")?;
                E::BvAdd(Box::new(a), Box::new(b))
            }
            "bvsub" => {
                let a = self.bv_arg()?;
                let b = self.bv_arg()?;
                same_width(&a, &b, "bvsub")?;
                E::BvSub(Box::new(a), Box::new(b))
            }
            "bvmul" => {
                let a = self.bv_arg()?;
                let b = self.bv_arg()?;
                same_width(&a, &b, "bvmul")?;
                E::BvMul(Box::new(a), Box::new(b))
            }
            "bvshl" => {
                let a = self.bv_arg()?;
                let b = self.bv_arg()?;
                same_width(&a, &b, "bvshl")?;
                E::BvShl(Box::new(a), Box::new(b))
            }
            "bvlshr" => {
                let a = self.bv_arg()?;
                let b = self.bv_arg()?;
                same_width(&a, &b, "bvlshr")?;
                E::BvLShr(Box::new(a), Box::new(b))
            }
            "bvashr" => {
                let a = self.bv_arg()?;
                let b = self.bv_arg()?;
                same_width(&a, &b, "bvashr")?;
                E::BvAshr(Box::new(a), Box::new(b))
            }
            "=" => {
                let a = self.bv_arg()?;
                let b = self.bv_arg()?;
                same_width(&a, &b, "=")?;
                E::Eq(Box::new(a), Box::new(b))
            }
            "bvult" => {
                let a = self.bv_arg()?;
                let b = self.bv_arg()?;
                same_width(&a, &b, "bvult")?;
                E::BvUlt(Box::new(a), Box::new(b))
            }
            "bvule" => {
                let a = self.bv_arg()?;
                let b = self.bv_arg()?;
                same_width(&a, &b, "bvule")?;
                E::BvUle(Box::new(a), Box::new(b))
            }
            "ite" => {
                let c = self.bool_arg()?;
                let t = self.bv_arg()?;
                let e = self.bv_arg()?;
                same_width(&t, &e, "ite branches")?;
                E::Ite(Box::new(c), Box::new(t), Box::new(e))
            }
            other => return Err(format!("unknown operator {}", other)),
        };
        self.eat(b')')?;
        Ok(out)
    }

    /// `(_ bvN w)`, `((_ extract hi lo) x)`, `((_ zero_extend n) x)`.
    fn indexed(&mut self) -> Result<E, String> {
        self.eat(b'_')?;
        let head = self.token()?;
        if let Some(num) = head.strip_prefix("bv") {
            let v: u128 = num
                .parse()
                .map_err(|_| format!("bad bv literal {}", num))?;
            let w: u8 = self
                .token()?
                .parse()
                .map_err(|_| "bad bv width".to_string())?;
            self.eat(b')')?;
            if w < 64 && v >= (1u128 << w) {
                return Err(format!("(_ bv{} {}) does not fit {} bits", v, w, w));
            }
            return Ok(E::BvConst(v as u64, w));
        }
        let (hi, lo) = match head.as_str() {
            "extract" => {
                let h: u8 = self
                    .token()?
                    .parse()
                    .map_err(|_| "bad extract hi".to_string())?;
                let l: u8 = self
                    .token()?
                    .parse()
                    .map_err(|_| "bad extract lo".to_string())?;
                (h, l)
            }
            "zero_extend" => {
                let n: u8 = self
                    .token()?
                    .parse()
                    .map_err(|_| "bad zero_extend".to_string())?;
                (n, 0)
            }
            other => return Err(format!("unknown indexed operator {}", other)),
        };
        self.eat(b')')?;
        let arg = self.bv_arg()?;
        self.eat(b')')?;
        match head.as_str() {
            "extract" => {
                if hi < lo {
                    return Err("extract with hi < lo".into());
                }
                if let Sort::Bv(aw) = arg.sort() {
                    if hi >= aw {
                        return Err(format!("extract {} {} from a {}-bit vector", hi, lo, aw));
                    }
                }
                Ok(E::Extract(hi, lo, Box::new(arg)))
            }
            _ => Ok(E::ZeroExtend(hi, Box::new(arg))),
        }
    }

    fn bool_arg(&mut self) -> Result<E, String> {
        let t = self.term()?;
        if t.sort() != Sort::Bool {
            return Err(format!("expected a boolean, found {:?}", t.sort()));
        }
        Ok(t)
    }

    fn bv_arg(&mut self) -> Result<E, String> {
        let t = self.term()?;
        if let Sort::Bv(_) = t.sort() {
            Ok(t)
        } else {
            Err(format!("expected a bit-vector, found {:?}", t.sort()))
        }
    }
}

fn same_width(a: &E, b: &E, who: &str) -> Result<(), String> {
    if a.sort() != b.sort() {
        Err(format!(
            "{} on different widths: {:?} vs {:?}",
            who,
            a.sort(),
            b.sort()
        ))
    } else {
        Ok(())
    }
}

/// Parse an exported query, checking sorts, and return the last assertion (the goal, which
/// the exporter has already negated).
fn parse_exported(text: &str) -> Result<E, String> {
    let mut goal = None;
    for line in text.lines() {
        let line = line.trim();
        if line.is_empty() || line.starts_with(';') || !line.starts_with("(assert") {
            continue;
        }
        let inner = line
            .strip_prefix("(assert")
            .and_then(|r| r.strip_suffix(')'))
            .ok_or_else(|| format!("malformed assert: {}", line))?;
        let mut r = Reader::new(inner);
        goal = Some(r.term()?);
        r.skip_ws();
        if r.i != r.s.len() {
            return Err(format!("trailing text in assert: {}", line));
        }
    }
    goal.ok_or_else(|| "no assert found".to_string())
}

#[test]
fn the_exported_smtlib2_is_well_sorted_and_means_the_same_thing() {
    let mut r = FuzzLcg(0x5eed_1234_abcd_0001);
    let mut checked = 0u32;
    for _ in 0..150 {
        let p = pfuzz_pred(&mut r, 3);
        let text = smt::with_fresh(|| {
            let a = var(8);
            let b = var(8);
            let pred = p.build(a, b);
            Query::new(&[a, b], pred).to_smtlib2_string()
        });
        let parsed = match parse_exported(&text) {
            Ok(e) => e,
            Err(e) => panic!("export was not well-sorted: {}\n{}", e, text),
        };
        // The exporter asserts the *negation* of the goal, so the parsed text must be
        // false exactly when the predicate is true.
        for a in 0..=255u64 {
            for b in 0..=255u64 {
                let want = !p.eval(a as u8, b as u8);
                let got = parsed.eval(a, b).b();
                assert_eq!(
                    got,
                    want,
                    "export disagrees at (a, b) = ({}, {}) for {}\n{}",
                    a,
                    b,
                    p.render(),
                    text
                );
            }
        }
        checked += 1;
    }
    assert_eq!(checked, 150);
}

#[test]
fn the_export_checker_rejects_what_the_old_exporter_printed() {
    // Teeth: three shapes the exporter once emitted, each rejected by sort checking.
    // 1. `bvnot` applied to a comparison (a boolean).
    assert!(
        parse_exported("(assert (bvnot (= x0_8 x1_8)))").is_err(),
        "bvnot on a boolean must be rejected"
    );
    // 2. `extract` past the end of the vector.
    assert!(
        parse_exported("(assert (= x0_8 ((_ extract 15 0) x1_8)))").is_err(),
        "extract 15 from 8 bits must be rejected"
    );
    // 3. A constant that does not fit its width.
    assert!(
        parse_exported("(assert (= x0_8 (_ bv300 8)))").is_err(),
        "an oversized literal must be rejected"
    );
    // 4. And a well-formed `extract` must be *accepted* -- the previous version of this
    //    checker rejected it too, which is how it "rejected" case 2 for the wrong reason.
    let ok = parse_exported("(assert (= x0_8 ((_ extract 7 0) x1_8)))");
    assert!(ok.is_ok(), "a well-formed extract must parse: {:?}", ok.err());
    let ok = parse_exported("(assert (= x0_8 ((_ zero_extend 0) x1_8)))");
    assert!(ok.is_ok(), "a well-formed zero_extend must parse: {:?}", ok.err());
    // And a well-formed one is accepted, so the checker is not refusing everything.
    assert!(parse_exported("(assert (= x0_8 (bvand x1_8 (_ bv255 8))))").is_ok());
}

#[test]
fn the_export_keeps_a_constant_goal_upright() {
    // Pinned directly: `truth(false)` must not export as `(assert false)`.
    smt::with_fresh(|| {
        let a = var(8);
        let t = Query::new(&[a], smt::truth(true)).to_smtlib2_string();
        let f = Query::new(&[a], smt::truth(false)).to_smtlib2_string();
        // `true` exports as `(not true)` = false; `false` exports as `(not false)` = true.
        assert!(!parse_exported(&t).unwrap().eval(0, 0).b(), "{}", t);
        assert!(parse_exported(&f).unwrap().eval(0, 0).b(), "{}", f);
    });
}

#[test]
fn the_export_clamps_an_oversized_shift_amount() {
    // A shift amount is printed as a literal of the shift's width, and a literal has to fit
    // that width. `shl(x, 300)` on an 8-bit value printed `(_ bv300 8)`, which no solver
    // accepts as an 8-bit literal, and for `k >= 2^w` the wrap changed the meaning: a shift
    // by 256 printed as `(_ bv0 8)`, i.e. the identity, while the engine says a shift of at
    // least the width yields 0. The engine's rule makes every amount `>= width` equivalent,
    // so the exporter clamps to `width`, a legal literal with the same meaning.
    for k in [8u32, 9, 255, 256, 300, u32::MAX] {
        let text = smt::with_fresh(|| {
            let x = var(8);
            let vars = [x];
            let terms = [
                smt::eq(smt::shl(x, k), smt::word(0, 8)),
                smt::eq(smt::lshr(x, k), smt::word(0, 8)),
                smt::eq(smt::ashr(x, k), smt::word(0, 8)),
            ];
            let mut out = String::new();
            for (i, t) in terms.iter().enumerate() {
                out.push_str(&Query::new(&vars, *t).to_smtlib2_string());
                if i + 1 < terms.len() {
                    out.push('\n');
                }
            }
            out
        });
        // Every emitted literal must be a legal one; the reader enforces `v < 2^w`.
        let parsed = parse_exported(&text)
            .unwrap_or_else(|e| panic!("shift by {} did not export a legal literal ({}):\n{}", k, e, text));
        assert_eq!(parsed.sort(), Sort::Bool);
        // The parsed text is the *conjunction* of the three negated goals, so it must be
        // false exactly when all three goals hold. `shl`/`lshr` by at least the width give
        // 0; `ashr` replicates the sign bit, which is 0 only for a non-negative input.
        for a in 0..256u64 {
            let shl_ok = true; // shl(x, k) == 0 for k >= width
            let lshr_ok = true; // lshr(x, k) == 0 for k >= width
            let ashr_ok = a & 0x80 == 0; // ashr(x, k) == 0 iff the sign bit is clear
            let all_hold = shl_ok && lshr_ok && ashr_ok;
            assert_eq!(
                parsed.eval(a, 0).b(),
                !all_hold,
                "shift by {} disagrees at x = {}:\n{}",
                k,
                a,
                text
            );
        }
    }
}

// ---------------------------------------------------------------------------
// The export fuzzer, extended to the operators the first version never emitted.
//
// The first export fuzz covered 8-bit word expressions and the comparisons over them. It
// therefore never printed `truncate`, `ite`, `ashr` or `zero_extend` -- which is exactly
// where the three real exporter bugs had lived. A fuzzer only checks the shapes it
// generates, so the generator is widened here to truncations, `ite`, and the arithmetic
// shift, plus assumptions, which the exporter prints as extra asserts.
//
// Widths are normalised deliberately: every binary operand is rebuilt at 8 bits, so the
// generator never asks the engine for a mixed-width term (which the engine refuses by
// design). A `Trunc` to a narrower width is always re-widened by its parent, which is what
// exercises both the `extract` and the `zero_extend` printing directions.
// ---------------------------------------------------------------------------

#[derive(Debug, Clone)]
enum WE {
    A,
    B,
    K(u64),
    Add(Box<WE>, Box<WE>),
    Sub(Box<WE>, Box<WE>),
    And(Box<WE>, Box<WE>),
    Or(Box<WE>, Box<WE>),
    Xor(Box<WE>, Box<WE>),
    Shl(Box<WE>, u32),
    LShr(Box<WE>, u32),
    Ashr(Box<WE>, u32),
    Trunc(Box<WE>, u8),
    Ite(Box<WE>, Box<WE>, Box<WE>),
}

impl WE {
    /// Build the term at exactly `w` bits. Children of a binary operator are built at 8
    /// bits, so no mixed-width term is ever requested.
    fn build_w(&self, a: Var, b: Var, w: u8) -> Var {
        let raw = match self {
            WE::A => a,
            WE::B => b,
            WE::K(k) => smt::word(*k, 8),
            WE::Add(x, y) => smt::add(x.build_w(a, b, 8), y.build_w(a, b, 8)),
            WE::Sub(x, y) => smt::sub(x.build_w(a, b, 8), y.build_w(a, b, 8)),
            WE::And(x, y) => smt::band(x.build_w(a, b, 8), y.build_w(a, b, 8)),
            WE::Or(x, y) => smt::bor(x.build_w(a, b, 8), y.build_w(a, b, 8)),
            WE::Xor(x, y) => smt::bxor(x.build_w(a, b, 8), y.build_w(a, b, 8)),
            WE::Shl(x, k) => smt::shl(x.build_w(a, b, 8), *k),
            WE::LShr(x, k) => smt::lshr(x.build_w(a, b, 8), *k),
            WE::Ashr(x, k) => smt::ashr(x.build_w(a, b, 8), *k),
            WE::Trunc(x, tw) => x.build_w(a, b, *tw),
            WE::Ite(_, t, e) => {
                let t8 = t.build_w(a, b, 8);
                let e8 = e.build_w(a, b, 8);
                let cond = smt::ult(t8, e8);
                smt::ite(cond, t8, e8)
            }
        };
        smt::truncate(raw, w)
    }

    fn build(&self, a: Var, b: Var) -> Var {
        self.build_w(a, b, 8)
    }

    /// The value of the term, masked to `w` bits -- the same `w` that `build_w` was given
    /// and that `smt::bits` reports for the built term.
    fn eval(&self, a: u64, b: u64, w: u8) -> u64 {
        let raw = match self {
            WE::A => a,
            WE::B => b,
            WE::K(k) => *k,
            WE::Add(x, y) => x.eval(a, b, 8).wrapping_add(y.eval(a, b, 8)),
            WE::Sub(x, y) => x.eval(a, b, 8).wrapping_sub(y.eval(a, b, 8)),
            WE::And(x, y) => x.eval(a, b, 8) & y.eval(a, b, 8),
            WE::Or(x, y) => x.eval(a, b, 8) | y.eval(a, b, 8),
            WE::Xor(x, y) => x.eval(a, b, 8) ^ y.eval(a, b, 8),
            WE::Shl(x, k) => {
                let v = x.eval(a, b, 8);
                if *k >= 8 {
                    0
                } else {
                    v << k
                }
            }
            WE::LShr(x, k) => {
                let v = x.eval(a, b, 8);
                if *k >= 8 {
                    0
                } else {
                    v >> k
                }
            }
            WE::Ashr(x, k) => {
                let v = x.eval(a, b, 8) & 0xff;
                let sign = (v >> 7) & 1 == 1;
                if *k >= 8 {
                    if sign {
                        0xff
                    } else {
                        0
                    }
                } else if sign {
                    (v >> k) | (!(0xffu64 >> k) & 0xff)
                } else {
                    v >> k
                }
            }
            WE::Trunc(x, tw) => x.eval(a, b, 8) & bit_mask(*tw),
            WE::Ite(_, t, e) => {
                let tv = t.eval(a, b, 8);
                let ev = e.eval(a, b, 8);
                if tv < ev {
                    tv
                } else {
                    ev
                }
            }
        };
        raw & bit_mask(w)
    }
}

fn we_expr(r: &mut FuzzLcg, depth: u32) -> WE {
    if depth == 0 || r.below(5) == 0 {
        return match r.below(3) {
            0 => WE::A,
            1 => WE::B,
            _ => WE::K(r.below(256)),
        };
    }
    let x = we_expr(r, depth - 1);
    let y = we_expr(r, depth - 1);
    let z = we_expr(r, depth - 1);
    match r.below(11) {
        0 => WE::Add(Box::new(x), Box::new(y)),
        1 => WE::Sub(Box::new(x), Box::new(y)),
        2 => WE::And(Box::new(x), Box::new(y)),
        3 => WE::Or(Box::new(x), Box::new(y)),
        4 => WE::Xor(Box::new(x), Box::new(y)),
        // Shift amounts span 0..=11, which includes `k >= width` (the region where the
        // engine returns 0 or the sign) and the boundary `k == width`. `k >= 2^w` (e.g. 256
        // for 8 bits) is covered by the dedicated test below, because a generator that only
        // emits small amounts cannot reach the clamp that bug lived in.
        5 => WE::Shl(Box::new(x), r.below(12) as u32),
        6 => WE::LShr(Box::new(x), r.below(12) as u32),
        7 => WE::Ashr(Box::new(x), r.below(12) as u32),
        8 => WE::Trunc(Box::new(x), 1 + r.below(8) as u8),
        9 => WE::Ite(Box::new(x), Box::new(y), Box::new(z)),
        _ => WE::Add(Box::new(x), Box::new(y)),
    }
}

/// The `WE` tree as a display string, so a failure names the input.
fn we_render(e: &WE) -> String {
    match e {
        WE::A => "a".into(),
        WE::B => "b".into(),
        WE::K(k) => format!("{}", k),
        WE::Add(x, y) => format!("({}+{})", we_render(x), we_render(y)),
        WE::Sub(x, y) => format!("({}-{})", we_render(x), we_render(y)),
        WE::And(x, y) => format!("({}&{})", we_render(x), we_render(y)),
        WE::Or(x, y) => format!("({}|{})", we_render(x), we_render(y)),
        WE::Xor(x, y) => format!("({}^{})", we_render(x), we_render(y)),
        WE::Shl(x, k) => format!("({}<<{})", we_render(x), k),
        WE::LShr(x, k) => format!("({}>>{})", we_render(x), k),
        WE::Ashr(x, k) => format!("({}>>a{})", we_render(x), k),
        WE::Trunc(x, w) => format!("trunc{}({})", w, we_render(x)),
        WE::Ite(c, t, e) => format!("ite({}, {}, {})", we_render(c), we_render(t), we_render(e)),
    }
}

#[test]
fn the_export_handles_truncate_ite_and_ashr() {
    // Deep terms are built and dropped recursively, and the default 2 MiB test-thread stack
    // is not enough for a depth-3 tree once every level is wrapped in `truncate`. Run on a
    // thread with a stack sized for the job rather than shrinking the generator, which would
    // weaken what the test reaches.
    std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(the_export_handles_truncate_ite_and_ashr_inner)
        .expect("spawn")
        .join()
        .expect("the export fuzzer panicked");
}

fn the_export_handles_truncate_ite_and_ashr_inner() {
    let mut r = FuzzLcg(0xc0ff_ee00_1234_5678);
    let mut trunc_seen = 0;
    let mut ite_seen = 0;
    let mut ashr_seen = 0;
    let mut checked = 0u32;
    for _ in 0..120 {
        let e = we_expr(&mut r, 3);
        let (text, w, want) = smt::with_fresh(|| {
            let a = var(8);
            let b = var(8);
            let t = e.build(a, b);
            let goal = smt::eq_const(t, 0);
            let s = Query::new(&[a, b], goal).to_smtlib2_string();
            let w = smt::bits(t);
            let mut want = [[false; 256]; 256];
            for x in 0..256u64 {
                for y in 0..256u64 {
                    // The export asserts the negation of the goal.
                    want[x as usize][y as usize] = e.eval(x, y, w) != 0;
                }
            }
            (s, w, want)
        });
        let parsed = parse_exported(&text).unwrap_or_else(|err| {
            panic!("export was not well-sorted ({}): {}\n{}", err, we_render(&e), text)
        });
        assert_eq!(parsed.sort(), Sort::Bool, "the asserted goal must be a boolean");
        for x in 0..256u64 {
            for y in 0..256u64 {
                let got = parsed.eval(x, y).b();
                assert_eq!(
                    got, want[x as usize][y as usize],
                    "export disagrees at (a, b) = ({}, {}) for {} (width {})\n{}",
                    x, y, we_render(&e), w, text
                );
            }
        }
        let shown = we_render(&e);
        if shown.contains("trunc") {
            trunc_seen += 1;
        }
        if shown.contains("ite") {
            ite_seen += 1;
        }
        if shown.contains(">>a") {
            ashr_seen += 1;
        }
        checked += 1;
    }
    assert_eq!(checked, 120);
    // Coverage is asserted, not assumed: a future edit that stopped emitting any of these
    // would leave this test passing and proving nothing about the printer path in question.
    assert!(trunc_seen > 0, "no truncate was generated");
    assert!(ite_seen > 0, "no ite was generated");
    assert!(ashr_seen > 0, "no arithmetic shift was generated");
}

#[test]
fn the_export_prints_assumptions_as_extra_asserts() {
    // A query with assumptions must print one assert per assumption plus the negated goal,
    // and every assert must parse on its own. This is the shape the module exists to emit,
    // and the first fuzzer never produced it.
    let text = smt::with_fresh(|| {
        let a = var(8);
        let b = var(8);
        let pre = smt::ult(a, b);
        let goal = smt::ule(a, b);
        Query::new(&[a, b], goal).assuming(&[pre]).to_smtlib2_string()
    });
    let asserts: Vec<&str> = text.lines().filter(|l| l.starts_with("(assert")).collect();
    assert_eq!(asserts.len(), 2, "one assert per assumption plus the goal:\n{}", text);
    for line in asserts {
        let inner = line
            .trim()
            .strip_prefix("(assert")
            .and_then(|x| x.strip_suffix(')'))
            .unwrap();
        let mut rd = Reader::new(inner);
        let e = rd
            .term()
            .unwrap_or_else(|err| panic!("ill-sorted assert ({}): {}", err, line));
        assert_eq!(e.sort(), Sort::Bool, "an assert must be a boolean: {}", line);
        rd.skip_ws();
        assert_eq!(rd.i, rd.s.len(), "trailing text in {}", line);
    }
}

#[test]
fn the_export_refuses_an_ill_formed_term_instead_of_printing_it() {
    // A term the engine *refuses* still has a tree, and printing that tree produces a file
    // no solver parses: `(bvadd x0_12 x1_8)` is ill-sorted. The engine returns `Unknown`
    // for a mixed-width operation, so there is no verdict to check -- but the exporter used
    // to print the tree anyway, and z3 rejects the whole file. That is the worst outcome
    // for the one artifact whose purpose is independent checking: it looks like a proof
    // that failed to load rather than a term that was refused.
    //
    // So the export must check the same flag the engine does. This test pins both halves:
    // the engine says `Unknown`, and the export contains no `(check-sat)` at all.
    smt::with_fresh(|| {
        let a = var(12);
        let b = var(8);
        let mixed = smt::add(a, b);
        assert!(
            matches!(smt::prove(smt::not(smt::eq(mixed, smt::word(0, 12)))), smt::Verdict::Unknown),
            "a mixed-width operation must be refused, not decided"
        );
        assert!(smt::is_ill_formed(), "the arena must record the refusal");
        let text = Query::new(&[a, b], smt::eq(mixed, smt::word(0, 12))).to_smtlib2_string();
        assert!(
            !text.contains("(check-sat)"),
            "a refused term must not produce a query:\n{}",
            text
        );
        assert!(text.contains("refused"), "the refusal must be stated:\n{}", text);
    });
}

#[test]
fn a_well_formed_query_is_still_exported_in_full() {
    // The control: the refusal check must not fire on a healthy query. Without this, the
    // previous test would pass if the exporter refused *everything*.
    smt::with_fresh(|| {
        let x = var(8);
        let text = Query::new(&[x], x.lt_val(100)).to_smtlib2_string();
        assert!(!smt::is_ill_formed(), "a same-width query is well-formed");
        assert!(text.contains("(check-sat)"), "a healthy query must be exported:\n{}", text);
        assert!(text.contains("(declare-fun"), "declarations must be present:\n{}", text);
    });
}
