//! Bit-slicing a term into gates for the SAT backend.
//!
//! # Why this is a second blaster, and what keeps it honest
//!
//! [`crate::smt`]'s blaster writes BDD node ids; this one writes [`crate::sat::Lit`]s.
//! They could have been one generic function, but the term arena and the gate arena are
//! both `&mut`, and threading one `Gates` trait through would either split the arena or
//! hide a pointer behind it. So they are two functions -- and the divergence risk that
//! creates is treated as a property to *check*, not to hope away:
//!
//! * `tests/differential.rs` proves a corpus of random formulas and requires that a
//!   verdict is never wrong, whichever engine produced it.
//! * `tests/sat_engine.rs` tests the SAT solver on its own against a brute-force
//!   enumeration of raw CNFs, so a solver bug is caught without the bit-blaster in the
//!   picture.
//!
//! If the two adders ever disagree, one of those two fails.
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
