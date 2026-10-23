//! Verifying code that touches memory, and the place where it stops working.
//!
//! Bit-vector logic cannot express "this array element is unchanged". `mem` adds
//! that: a bounded memory whose cells are ordinary symbolic words, with `read` as
//! an ite chain and `store` as a simultaneous update.
//!
//! Run with: `cargo run --features std --example memory`

use sparkrs::mem::{declare, Mem, MAX_CELLS};
use sparkrs::smt::{self, var, Verdict};
use sparkrs::wp::{self, Stmt};

fn main() {
    println!("=== a bounded memory: 4 cells of 8 bits ===\n");

    smt::with_fresh(|| {
        let mut buf = [var(8); 4];
        let n = declare(2, 8, &mut buf);
        let m = Mem::new(&buf[..n], 8);
        println!("address width : {}", m.addr_width());
        println!("cells         : {}", m.len());
        println!("element width : {} bits\n", m.elem_width());

        let addr = var(2);
        let val = var(8);
        let at = var(2);

        // The frame condition, proved for every address and value. This is the
        // obligation you would otherwise have to write by hand at every call site.
        println!("frame lemma (all inputs):");
        println!(
            "  read(store(m, a, v), b) == ite(a == b, v, read(m, b))  ->  {}",
            verdict(&smt::prove(m.frame_lemma(addr, val, at)))
        );

        // A write, then a read back at the same address.
        let readback = m.store_wp(addr, val, smt::eq(m.read(addr), val));
        println!(
            "  write then read back                                   ->  {}",
            verdict(&smt::prove(readback))
        );

        // A write does not disturb a different, pinned address.
        let other = m.read_const(3);
        let frame = m.store_wp(addr, val, smt::eq(other, m.read_const(3)));
        let goal = smt::implies(smt::not(smt::eq_const(addr, 3)), frame);
        println!(
            "  write to a != 3 leaves cell 3 alone                    ->  {}",
            verdict(&smt::prove(goal))
        );
        println!();
    });

    // ---------------------------------------------------------------------
    // A program over memory, verified end to end.
    // ---------------------------------------------------------------------
    println!("=== a swap through a temporary, verified as a program ===\n");

    smt::with_fresh(|| {
        let mut buf = [var(8); 4];
        let n = declare(2, 8, &mut buf);
        let m = Mem::new(&buf[..n], 8);
        let i = var(2);
        let j = var(2);
        let t = var(8);
        let oi = var(8);
        let oj = var(8);

        // The old values have to be captured into fresh variables. A
        // postcondition is read in the final state, and substitution rewrites
        // every cell variable in it, so `m.read(i)` written directly in the
        // postcondition would mean the *new* contents. This is the same
        // discipline as SPARK's `m'Old`.
        let save_i = Stmt::Assign { var: oi, expr: m.read(i) };
        let save_j = Stmt::Assign { var: oj, expr: m.read(j) };
        let save_t = Stmt::Assign { var: t, expr: oi };

        let mut b1 = [(i, t); MAX_CELLS];
        let n1 = m.store_binds(i, oj, &mut b1);
        let mut b2 = [(i, t); MAX_CELLS];
        let n2 = m.store_binds(j, t, &mut b2);
        let write_i = Stmt::AssignMany { binds: &b1[..n1] };
        let write_j = Stmt::AssignMany { binds: &b2[..n2] };

        let prog = Stmt::Seq {
            first: &save_i,
            second: &Stmt::Seq {
                first: &save_j,
                second: &Stmt::Seq {
                    first: &save_t,
                    second: &Stmt::Seq {
                        first: &write_i,
                        second: &write_j,
                    },
                },
            },
        };

        // Postcondition: the two cells exchanged contents.
        let post = smt::and(smt::eq(m.read(i), oj), smt::eq(m.read(j), oi));
        let report = wp::verify(&prog, smt::truth(true), post);
        println!("obligations : {}", report.count);
        println!("contract    : {}", verdict(&report.contract.discharge()));
        println!("verified    : {}\n", report.is_verified());

        // The frame part, as a separate obligation: a cell that is neither i nor
        // j keeps its contents. Both addresses have to be excluded; leaving one
        // out is a mistake the engine will find for you.
        let k = smt::word(3, 2);
        let kept = smt::eq(m.read(k), smt::word(0, 8));
        let untouched = smt::and(
            smt::eq_const(m.read_const(3), 0),
            smt::and(smt::not(smt::eq(i, k)), smt::not(smt::eq(j, k))),
        );
        let frame = smt::implies(untouched, wp::wp(kept, &prog));
        println!("frame obligation (cell 3 untouched when i, j != 3):");
        println!("  {}", verdict(&smt::prove(frame)));
        println!();
    });

    // ---------------------------------------------------------------------
    // Where this stops. Stated plainly, because a limit you discover yourself is
    // more expensive than one you were told about.
    // ---------------------------------------------------------------------
    println!("=== the limit: a loop over addresses ===\n");
    println!("for k in 0..4 {{ m[k] := 0 }} is fine to *verify* when unrolled, but the");
    println!("loop form is not verifiable here. Its invariant would have to say \"every");
    println!("cell below k is zero\", and that is a prefix predicate this representation");
    println!("does not have: a symbolic read is a flat ite chain over individual cells,");
    println!("with no notion of a range. Bounds are structural — an address is 2 bits,");
    println!("so it cannot name a cell outside the memory — but *universal* statements");
    println!("over addresses need a quantifier the bit-vector logic does not provide.\n");
    println!("What works instead: unroll, or state the property cell by cell.\n");

    // Unrolled, it verifies.
    smt::with_fresh(|| {
        let mut buf = [var(8); 4];
        let n = declare(2, 8, &mut buf);
        let m = Mem::new(&buf[..n], 8);
        let zero = smt::word(0, 8);

        let mut storage = [[(zero, zero); MAX_CELLS]; 4];
        let mut counts = [0usize; 4];
        for (k, count) in counts.iter_mut().enumerate() {
            let addr = smt::word(k as u64, 2);
            *count = m.store_binds(addr, zero, &mut storage[k]);
        }
        let w0 = Stmt::AssignMany { binds: &storage[0][..counts[0]] };
        let w1 = Stmt::AssignMany { binds: &storage[1][..counts[1]] };
        let w2 = Stmt::AssignMany { binds: &storage[2][..counts[2]] };
        let w3 = Stmt::AssignMany { binds: &storage[3][..counts[3]] };
        let prog = Stmt::Seq {
            first: &w0,
            second: &Stmt::Seq {
                first: &w1,
                second: &Stmt::Seq { first: &w2, second: &w3 },
            },
        };
        let post = smt::all(&[
            smt::eq_const(m.read_const(0), 0),
            smt::eq_const(m.read_const(1), 0),
            smt::eq_const(m.read_const(2), 0),
            smt::eq_const(m.read_const(3), 0),
        ]);
        let report = wp::verify(&prog, smt::truth(true), post);
        println!("unrolled memset, all four cells zero:");
        println!("  verified: {}\n", report.is_verified());
    });

    println!("done");
}

fn verdict(v: &Verdict) -> &'static str {
    match v {
        Verdict::Valid => "valid",
        Verdict::Counterexample(_) => "refuted",
        Verdict::Unknown => "unknown",
        Verdict::Unsat => "unsat",
    }
}
