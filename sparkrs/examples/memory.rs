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
    println!("=== a loop over addresses, which needs a quantifier ===\n");
    println!("A fill loop's invariant has to say \"every cell below k is zero\". That is");
    println!("a quantifier, which a bit-vector decision procedure does not have -- but");
    println!("it is *bounded*, and a bounded quantifier is a finite conjunction, so it");
    println!("can simply be expanded: (0 < k => m[0] == 0) && (1 < k => m[1] == 0) && ...");
    println!("`Mem::forall_below` does that, which is what makes this loop verifiable at");
    println!("all instead of needing a hand unroll.\n");

    smt::with_fresh(|| {
        let mut buf = [var(8); 4];
        let n = declare(2, 8, &mut buf);
        let m = Mem::new(&buf[..n], 8);
        // The counter is 3 bits, one wider than the 2-bit address: a 2-bit counter
        // could never reach 4, so `while k < 4` would not exit. `addr_of` truncates
        // it back to an address at the point of use, the way a machine with an
        // index register wider than its address bus does.
        let k = var(3);
        let zero = smt::word(0, 8);

        let addr = m.addr_of(k);
        let mut binds = [(addr, zero); MAX_CELLS];
        let nb = m.store_binds(addr, zero, &mut binds);
        let store = Stmt::AssignMany { binds: &binds[..nb] };
        let step = Stmt::Assign { var: k, expr: k + 1u32 };
        let body = Stmt::Seq { first: &store, second: &step };

        let inv = m.forall_below(k, |cell| smt::eq_const(cell, 0));
        let loop_ = Stmt::While {
            cond: smt::ult_const(k, 4),
            invariant: inv,
            variant: Some(smt::sub(smt::word(4, 3), k)),
            body: &body,
        };
        let init = Stmt::Assign { var: k, expr: smt::word(0, 3) };
        let prog = Stmt::Seq { first: &init, second: &loop_ };

        let post = m.forall_cells(|cell| smt::eq_const(cell, 0));
        let report = wp::verify(&prog, smt::truth(true), post);
        println!("for k := 0; k < 4; k += 1 {{ m[k] := 0 }}");
        println!("  invariant: forall j < k {{ m[j] == 0 }}");
        println!("  obligations : {}", report.count);
        println!("  verified    : {}", report.is_verified());
        println!("  termination : {:?}", report.correctness());
        if let Some((ob, _)) = report.first_failure() {
            println!("  FAILED      : {:?}", ob.rule);
        }
    });

    // The control: the same loop with only "the cell at k is zero" as its
    // invariant. The postcondition needs all four cells, so it must fail. Without
    // this, the test above would not show that the quantifier is doing work.
    smt::with_fresh(|| {
        let mut buf = [var(8); 4];
        let n = declare(2, 8, &mut buf);
        let m = Mem::new(&buf[..n], 8);
        let k = var(3);
        let zero = smt::word(0, 8);

        let addr = m.addr_of(k);
        let mut binds = [(addr, zero); MAX_CELLS];
        let nb = m.store_binds(addr, zero, &mut binds);
        let store = Stmt::AssignMany { binds: &binds[..nb] };
        let step = Stmt::Assign { var: k, expr: k + 1u32 };
        let body = Stmt::Seq { first: &store, second: &step };

        let loop_ = Stmt::While {
            cond: smt::ult_const(k, 4),
            invariant: smt::eq_const(m.read(addr), 0),
            variant: None,
            body: &body,
        };
        let init = Stmt::Assign { var: k, expr: smt::word(0, 3) };
        let prog = Stmt::Seq { first: &init, second: &loop_ };
        let post = m.forall_cells(|cell| smt::eq_const(cell, 0));
        let report = wp::verify(&prog, smt::truth(true), post);
        println!();
        println!("same loop, invariant weakened to \"m[k] == 0\" only:");
        println!("  verified    : {} (as it must be: one cell is not four)", report.is_verified());
    });

    println!();
    println!("=== what is still out of reach ===\n");
    println!("The bound has to be a number the tool can count to, because the expansion");
    println!("has one conjunct per cell. `forall k < 1000` is a thousand copies of the");
    println!("predicate, and `MAX_CELLS` caps a memory at 64 cells for that reason. So:");
    println!("quantifiers over a *fixed* range are fine, unbounded ones are not, and the");
    println!("cost grows linearly with the range either way. A true `forall` over an");
    println!("unknown domain would need a different decision procedure -- that is the line");
    println!("between this crate and a real SMT solver, and it is not a small one.\n");

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
