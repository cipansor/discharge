//! Bit-slicing a term into gates for the SAT backend.
//!
//! # Why this is a second blaster, and what keeps it honest
//!
//! [`crate::smt`]'s blaster writes BDD node ids; this one writes [`crate::sat::Lit`]s.
//! They could have been one generic function, but the term arena and the gate arena are
//! both `&mut`, and threading one `Gates` trait through would either split the arena or
//! hide a pointer behind it. So they are two functions, and each writes its own adder,
//! subtractor, multiplier and comparator circuit. The *arithmetic is not shared code*: the
//! two circuits can diverge, and a divergence here is the worst kind, because the SAT
//! blaster only runs when the BDD arena has already filled, which is exactly where a
//! hand-checked example is least likely to look.
//!
//! So the agreement is treated as a property to *check*, not to hope away:
//!
//! * The `tests` module below blasts each operation with *this* blaster and asks the
//!   solver whether the resulting circuit can differ from Rust's own wrapping arithmetic
//!   on any input. It is exhaustive over widths 1..=4, and it is the only test that
//!   exercises this blaster at widths where the BDD engine also finishes -- so the
//!   oracle does not depend on the engine under test.
//! * `tests/differential.rs` proves a corpus of random formulas through the public API
//!   and requires that a verdict is never wrong, whichever engine produced it.
//! * `tests/sat_engine.rs` tests the SAT solver on its own against a brute-force
//!   enumeration of raw CNFs, so a solver bug is caught without the bit-blaster in the
//!   picture.
//!
//! The first of those is load-bearing: a mutation that drops the carry-generate term from
//! this file's adder (making it compute `xor`) survives `tests/differential.rs`, the full
//! `cargo test` run *and* the z3 oracle, because none of them reach this blaster -- the
//! BDD engine decides every query they make. The exhaustive test below is what fails.
//!
//! The bit-level structure is deliberately identical to `smt::blast`: same ripple adders,
//! same borrow chain, same shift rule, same ripple comparator. A reader comparing the two
//! should find no semantic difference, which is the point.

use crate::sat::{Cnf, Lit};
use crate::smt::{Ctx, Op, Term};

/// A wide enough buffer for any word the language allows.
pub const MAX_BITS: usize = 64;

/// Blast `t` into `out[..width]`, adding gates to `cnf`.
pub(crate) fn blast(ctx: &mut Ctx, cnf: &mut Cnf, t: Term, out: &mut [Lit; MAX_BITS]) {
    // Same stale rule as the BDD blaster: one stale touch poisons the whole traversal,
    // because a constructor can read a stale node and build a current node that points
    // back at it, leaving a cycle whose every node looks current.
    if ctx.is_stale(t) {
        ctx.mark_stale();
        let f = cnf.false_lit();
        out.fill(f);
        return;
    }
    let n = ctx.peek(t);
    let w = n.width as usize;
    // Same refusal as the BDD blaster: the buffer is `[Lit; 64]`, so a term wider than a
    // word is ill-formed rather than something to index past. See `smt::Ctx::blast`.
    if w == 0 || w > MAX_BITS {
        ctx.mark_ill_formed();
        let f = cnf.false_lit();
        out.fill(f);
        return;
    }
    match n.op {
        Op::Var => {
            let idx = n.a;
            for (bit, slot) in out[..w].iter_mut().enumerate() {
                *slot = cnf.input_bit(idx, bit as u32);
            }
        }
        Op::Const => {
            let v = ctx.const_of(t);
            for (bit, slot) in out[..w].iter_mut().enumerate() {
                *slot = if (v >> bit) & 1 == 1 { cnf.true_lit() } else { cnf.false_lit() };
            }
        }
        Op::Not => {
            let mut a = [cnf.false_lit(); MAX_BITS];
            blast(ctx, cnf, Term(n.a), &mut a);
            for bit in 0..w {
                out[bit] = a[bit].not();
            }
        }
        Op::And | Op::Or | Op::Xor => {
            let mut a = [cnf.false_lit(); MAX_BITS];
            let mut b = [cnf.false_lit(); MAX_BITS];
            blast(ctx, cnf, Term(n.a), &mut a);
            blast(ctx, cnf, Term(n.b), &mut b);
            for bit in 0..w {
                out[bit] = match n.op {
                    Op::And => cnf.and(a[bit], b[bit]),
                    Op::Or => cnf.or(a[bit], b[bit]),
                    _ => cnf.xor(a[bit], b[bit]),
                };
            }
        }
        Op::Shl | Op::LShr | Op::Shr => {
            let mut a = [cnf.false_lit(); MAX_BITS];
            blast(ctx, cnf, Term(n.a), &mut a);
            let sh = n.b as usize;
            let sign = a[w - 1];
            let f = cnf.false_lit();
            for (bit, slot) in out[..w].iter_mut().enumerate() {
                *slot = match n.op {
                    // `bit >= sh` is checked first so `bit - sh` cannot wrap.
                    Op::Shl if bit >= sh => a[bit - sh],
                    Op::Shl => f,
                    // Same overflow guard as `smt::blast`: `bit + sh` wraps on a
                    // 32-bit target when `sh` is a wide literal like `u32::MAX`,
                    // and the wrapped index selects an input bit instead of the
                    // defined zero. `w - bit` stays small.
                    Op::LShr if sh < w - bit => a[bit + sh],
                    Op::LShr => f,
                    // Arithmetic right shift replicates the sign bit.
                    _ if sh < w - bit => a[bit + sh],
                    _ => sign,
                };
            }
        }
        Op::Add => {
            let mut a = [cnf.false_lit(); MAX_BITS];
            let mut b = [cnf.false_lit(); MAX_BITS];
            blast(ctx, cnf, Term(n.a), &mut a);
            blast(ctx, cnf, Term(n.b), &mut b);
            let mut carry = cnf.false_lit();
            for bit in 0..w {
                let axb = cnf.xor(a[bit], b[bit]);
                out[bit] = cnf.xor(axb, carry);
                let ab = cnf.and(a[bit], b[bit]);
                let cx = cnf.and(carry, axb);
                carry = cnf.or(ab, cx);
            }
        }
        Op::Sub => {
            let mut a = [cnf.false_lit(); MAX_BITS];
            let mut b = [cnf.false_lit(); MAX_BITS];
            blast(ctx, cnf, Term(n.a), &mut a);
            blast(ctx, cnf, Term(n.b), &mut b);
            let mut borrow = cnf.true_lit(); // a + ~b + 1
            for bit in 0..w {
                let nb = b[bit].not();
                let axb = cnf.xor(a[bit], nb);
                out[bit] = cnf.xor(axb, borrow);
                let ab = cnf.and(a[bit], nb);
                let cx = cnf.and(borrow, axb);
                borrow = cnf.or(ab, cx);
            }
        }
        Op::Mul => {
            let mut a = [cnf.false_lit(); MAX_BITS];
            let mut b = [cnf.false_lit(); MAX_BITS];
            blast(ctx, cnf, Term(n.a), &mut a);
            blast(ctx, cnf, Term(n.b), &mut b);
            let f = cnf.false_lit();
            out[..w].fill(f);
            for j in 0..w {
                let mut carry = f;
                for i in j..w {
                    let partial = cnf.and(a[i - j], b[j]);
                    let s1 = cnf.xor(out[i], partial);
                    let s2 = cnf.xor(s1, carry);
                    let c1 = cnf.and(out[i], partial);
                    let c2 = cnf.and(carry, s1);
                    carry = cnf.or(c1, c2);
                    out[i] = s2;
                }
            }
        }
        Op::Eq => {
            let mut a = [cnf.false_lit(); MAX_BITS];
            let mut b = [cnf.false_lit(); MAX_BITS];
            blast(ctx, cnf, Term(n.a), &mut a);
            blast(ctx, cnf, Term(n.b), &mut b);
            let mut acc = cnf.true_lit();
            for bit in 0..w {
                let x = cnf.xor(a[bit], b[bit]);
                acc = cnf.and(acc, x.not());
            }
            out[0] = acc;
        }
        Op::Ult | Op::Ule => {
            let mut a = [cnf.false_lit(); MAX_BITS];
            let mut b = [cnf.false_lit(); MAX_BITS];
            blast(ctx, cnf, Term(n.a), &mut a);
            blast(ctx, cnf, Term(n.b), &mut b);
            let mut lt = cnf.false_lit();
            let mut eq = cnf.true_lit();
            for bit in (0..w).rev() {
                let na = a[bit].not();
                let nab = cnf.and(na, b[bit]);
                let lt_here = cnf.and(eq, nab);
                lt = cnf.or(lt, lt_here);
                let e = cnf.xor(a[bit], b[bit]).not();
                eq = cnf.and(eq, e);
            }
            out[0] = if n.op == Op::Ule { cnf.or(lt, eq) } else { lt };
        }
        Op::Ite => {
            let mut c = [cnf.false_lit(); MAX_BITS];
            let mut t2 = [cnf.false_lit(); MAX_BITS];
            let mut e2 = [cnf.false_lit(); MAX_BITS];
            blast(ctx, cnf, Term(n.a), &mut c);
            blast(ctx, cnf, Term(n.b), &mut t2);
            blast(ctx, cnf, Term(n.c), &mut e2);
            for bit in 0..w {
                out[bit] = cnf.mux(c[0], t2[bit], e2[bit]);
            }
        }
        Op::Trunc => {
            let mut a = [cnf.false_lit(); MAX_BITS];
            blast(ctx, cnf, Term(n.a), &mut a);
            let src = n.b as usize;
            let f = cnf.false_lit();
            for (bit, slot) in out[..w].iter_mut().enumerate() {
                // Widening zero-fills, narrowing drops the high bits; one expression
                // covers both because the source is only read where it exists.
                *slot = if bit < src { a[bit] } else { f };
            }
        }
    }
}

#[cfg(test)]
mod tests {
    //! The oracle for *this* blaster.
    //!
    //! Every other test in the crate reaches this file only when the BDD arena has already
    //! filled, which no test at a small width does. So a bug in these circuits would sit
    //! behind the fallback, invisible until a user's wide query hit it. This module drives
    //! `blast` directly, forces the inputs, and asks the solver whether the circuit can
    //! differ from Rust's own wrapping arithmetic -- an oracle that shares no code with the
    //! blaster. The widths are small so the check is exhaustive over every input pair.

    use super::*;
    use crate::sat::{self, Sat};
    use crate::smt;

    fn mask(w: u8) -> u64 {
        if w >= 64 {
            u64::MAX
        } else {
            (1u64 << w) - 1
        }
    }

    /// Blast `build(x, y)` with this blaster, force `x = a` and `y = b`, and ask whether the
    /// circuit's low `res_w` bits can differ from `want`. `true` means the blaster is wrong.
    ///
    /// The query is "can the circuit output differ", so the good answer is `Unsat`: no input
    /// makes them differ. `Sat` names a divergence, and `Unknown` is treated as a divergence
    /// too, because an encoding that cannot be decided is not evidence that it is right.
    fn circuit_can_differ(
        w: u8,
        res_w: u8,
        build: impl Fn(smt::Var, smt::Var) -> smt::Term,
        a: u64,
        b: u64,
        want: u64,
    ) -> bool {
        smt::with_fresh(|| {
            // Explicit indices so the forced inputs below are the same variables the
            // blaster reads for `Op::Var`.
            let x = smt::var_named(0, w);
            let y = smt::var_named(1, w);
            let t = build(x, y);
            smt::with_ctx(|ctx| {
                sat::query(|cnf| {
                    let mut out = [cnf.false_lit(); MAX_BITS];
                    blast(ctx, cnf, t, &mut out);
                    for (idx, val) in [(0u32, a), (1u32, b)] {
                        for bit in 0..w {
                            let lit = cnf.input_bit(idx, bit as u32);
                            let one = (val >> bit) & 1 == 1;
                            cnf.add_clause(&[if one { lit } else { lit.not() }]);
                        }
                    }
                    let mut diff = cnf.false_lit();
                    for (bit, lit) in out.iter().enumerate().take(res_w as usize) {
                        let one = (want >> bit) & 1 == 1;
                        let mism = if one { lit.not() } else { *lit };
                        diff = cnf.or(diff, mism);
                    }
                    diff
                })
            })
            .0 != Sat::Unsat
        })
    }

    /// A word-valued operation, checked against Rust on every input pair at 1..=4 bits.
    fn word_op(
        w: u8,
        name: &str,
        build: impl Fn(smt::Var, smt::Var) -> smt::Term,
        rust: impl Fn(u64, u64) -> u64,
    ) {
        let m = mask(w);
        for a in 0..=m {
            for b in 0..=m {
                let want = rust(a, b) & m;
                assert!(
                    !circuit_can_differ(w, w, &build, a, b, want),
                    "{name} at {w} bits: the SAT blaster disagrees with Rust on a={a} b={b} (want {want})"
                );
            }
        }
    }

    /// A predicate-valued operation; the circuit writes its answer to `out[0]`.
    fn cmp_op(
        w: u8,
        name: &str,
        build: impl Fn(smt::Var, smt::Var) -> smt::Term,
        rust: impl Fn(u64, u64) -> bool,
    ) {
        let m = mask(w);
        for a in 0..=m {
            for b in 0..=m {
                let want = u64::from(rust(a, b));
                assert!(
                    !circuit_can_differ(w, 1, &build, a, b, want),
                    "{name} at {w} bits: the SAT blaster disagrees with Rust on a={a} b={b} (want {want})"
                );
            }
        }
    }

    /// Sign-extend a `w`-bit value, for the arithmetic shift's oracle.
    fn sign_extend(v: u64, w: u8) -> i64 {
        let v = v & mask(w);
        if w < 64 && (v >> (w - 1)) & 1 == 1 {
            (v | !mask(w)) as i64
        } else {
            v as i64
        }
    }

    #[test]
    fn the_sat_adder_matches_rust() {
        for w in 1..=4 {
            word_op(w, "add", |x, y| smt::add(x, y).0, |a, b| a.wrapping_add(b));
        }
    }

    #[test]
    fn the_sat_subtractor_matches_rust() {
        for w in 1..=4 {
            word_op(w, "sub", |x, y| smt::sub(x, y).0, |a, b| a.wrapping_sub(b));
        }
    }

    #[test]
    fn the_sat_multiplier_matches_rust() {
        for w in 1..=4 {
            word_op(w, "mul", |x, y| smt::mul(x, y).0, |a, b| a.wrapping_mul(b));
        }
    }

    #[test]
    fn the_sat_bitwise_ops_match_rust() {
        for w in 1..=4 {
            word_op(w, "and", |x, y| smt::band(x, y).0, |a, b| a & b);
            word_op(w, "or", |x, y| smt::bor(x, y).0, |a, b| a | b);
            word_op(w, "xor", |x, y| smt::bxor(x, y).0, |a, b| a ^ b);
        }
    }

    #[test]
    fn the_sat_comparators_match_rust() {
        for w in 1..=4 {
            cmp_op(w, "eq", |x, y| smt::eq(x, y).0, |a, b| a == b);
            cmp_op(w, "ult", |x, y| smt::ult(x, y).0, |a, b| a < b);
            cmp_op(w, "ule", |x, y| smt::ule(x, y).0, |a, b| a <= b);
        }
    }

    #[test]
    fn the_sat_shifters_match_rust() {
        // `k < w` only: the engine zero-fills past the width, while Rust's `wrapping_shl`
        // takes `k mod w`. The two are meant to differ there, so that range is not the
        // blaster's to get right.
        for w in 1..=4u8 {
            for k in 0..w {
                word_op(w, "shl", |x, _| smt::shl(x, k as u32).0, |a, _| a << k);
                word_op(w, "lshr", |x, _| smt::lshr(x, k as u32).0, |a, _| a >> k);
                word_op(
                    w,
                    "shr",
                    |x, _| smt::ashr(x, k as u32).0,
                    |a, _| (sign_extend(a, w) >> k) as u64,
                );
            }
        }
    }

    #[test]
    fn the_divergence_check_has_teeth() {
        // The helper above reports "no divergence" by asserting `Unsat`. If it were
        // returning `false` for every query -- a typo in the goal, a forgotten clause --
        // every test in this module would pass while checking nothing. So ask it a
        // question whose answer is `true` on purpose: `add(x, y)` cannot always equal
        // `xor(x, y)`, so a single input pair must be reported as differing.
        let m = mask(4);
        let mut found = false;
        for a in 0..=m {
            for b in 0..=m {
                let xor = a ^ b;
                let add = a.wrapping_add(b) & m;
                if xor != add
                    && circuit_can_differ(4, 4, |x, y| smt::bxor(x, y).0, a, b, add)
                {
                    found = true;
                }
            }
        }
        assert!(
            found,
            "the divergence check never reported a difference, so it cannot be detecting any"
        );
    }

    /// A query past the BDD's node capacity must *return* a verdict, not walk the
    /// rest of the term graph.
    ///
    /// The guard in `smt::Ctx::blast` stops the traversal the moment the node table
    /// is full. Without it the walk continues over a fan-out DAG whose *unrolled*
    /// size is exponential in the number of steps -- `udiv` and `pow` are both
    /// built that way -- and the query never reaches the SAT fallback that would
    /// have answered it. That is a hang, which is worse than a refusal: the caller
    /// asked a question and got no answer at all.
    ///
    /// The assertion is only that a verdict came back, not which one: the table
    /// filling is a capacity fact, and whether the SAT engine then decides the
    /// query is its business. A regression makes this test hang, which the harness
    /// reports as a timeout.
    #[test]
    fn a_query_past_the_bdd_capacity_returns_instead_of_hanging() {
        smt::with_fresh(|| {
            let x = smt::var(8);
            let y = smt::var(8);
            let q = smt::udiv(x, y);
            let _ = smt::prove(smt::eq(q, smt::word(1, 8)));
        });
        smt::with_fresh(|| {
            let base = smt::var(8);
            let r = crate::mir::intrinsics::eval(
                crate::mir::intrinsics::Intrinsic::Pow(crate::mir::intrinsics::Family::Wrapping),
                base,
                smt::word(7, 32),
                8,
                false,
                8,
            );
            let Some(crate::mir::intrinsics::Outcome::Value(out)) = r else {
                panic!("`wrapping_pow` at a `u8` must be modelled");
            };
            let _ = smt::prove(smt::eq(out, smt::word(128, 8)));
        });
    }
}
