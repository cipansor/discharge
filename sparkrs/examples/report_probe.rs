// A report's verdict must not depend on the arena it is read in.
//
// `verify` records obligations and `first_failure` discharges them lazily, each call
// against whatever arena is current. A goal is a term id, so after a reset the recorded
// id named a different formula, and a refuted program could read as verified:
//
//   goal id (as recorded): Pred(Term(10))
//   filler  0: contract discharge = "Counterexample"   <- correct
//   filler  1: contract discharge = "Valid"            <- a failing report read as proved
//
// Obligations now record the arena generation, and `discharge` returns Unknown when the
// arena has moved on.
use sparkrs::prelude::*;
use sparkrs::smt;
use sparkrs::wp::{verify, Stmt};

fn main() {
    let report = smt::with_fresh(|| {
        let x = var(8);
        let y = var(8);
        let body = Stmt::Assign { var: y, expr: x + 1u32 };
        // Pre: x < 10. Body: y := x+1. Post: y <= 5 -- false for x = 9.
        let r = verify(&body, x.lt_val(10), y.le_val(5));
        println!("in its own arena : is_verified() = {}", r.is_verified());
        r
    });

    for n in 0..4 {
        smt::with_fresh(|| {
            for _ in 0..n {
                let _ = smt::truth(true);
            }
            let v = report.contract.discharge();
            println!("filler {:>2}        : is_verified() = {}  (discharge = {:?})",
                     n, report.is_verified(),
                     match v { smt::Verdict::Valid => "Valid", smt::Verdict::Unsat => "Unsat",
                               smt::Verdict::Counterexample(_) => "Counterexample",
                               smt::Verdict::Unknown => "Unknown" });
        });
    }
    println!("--- a stale report now fails, in every arena, instead of flipping to Valid");
}
