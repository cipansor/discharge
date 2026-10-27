//! Differential test for the CDCL solver against brute force.
//!
//! The BDD and SAT engines are compared in `differential.rs`, but when they disagree that
//! test cannot say *which* engine is wrong. This one has an oracle the solver cannot share
//! code with: for a small number of variables, enumerate every assignment and check the
//! clauses directly. It also checks a returned model actually satisfies the clauses, which
//! catches a solver that reports `Sat` for the wrong reason.

use discharge::sat::{self, Lit, Sat};

struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0 >> 11
    }
    fn below(&mut self, n: u64) -> u64 {
        self.next() % n
    }
}

fn brute(clauses: &[Vec<u32>], nvars: u32) -> bool {
    for m in 0u32..(1u32 << nvars) {
        let ok = clauses.iter().all(|c| {
            c.iter().any(|&l| {
                let v = l >> 1;
                let sign = l & 1 == 1;
                let val = (m >> v) & 1 == 1;
                val != sign
            })
        });
        if ok {
            return true;
        }
    }
    false
}

#[test]
fn solver_agrees_with_brute_force_on_random_cnfs() {
    let mut r = Lcg(0xdead_beef_1234_5678);
    let mut sat_seen = 0u32;
    let mut unsat_seen = 0u32;
    for trial in 0..2000 {
        let nvars = 1 + r.below(6) as u32; // 1..=6 vars, so 2..=64 assignments
        let nclauses = 1 + r.below(14) as usize;
        let mut clauses: Vec<Vec<u32>> = Vec::new();
        for _ in 0..nclauses {
            let k = 1 + r.below(3) as usize;
            let mut c: Vec<u32> = Vec::new();
            for _ in 0..k {
                let v = r.below(nvars as u64) as u32;
                let sign = r.below(2) as u32;
                let l = (v << 1) | sign;
                if !c.contains(&l) && !c.contains(&(l ^ 1)) {
                    c.push(l);
                }
            }
            if c.is_empty() {
                continue;
            }
            clauses.push(c);
        }
        let expect = brute(&clauses, nvars);

        // Encode: one SAT variable per CNF variable, clauses via add_clause.
        let (got, model) = sat::query(|cnf| {
            // Materialise the input bits so variable indices line up with `v`.
            // `input_bit(0, v)` is input key `v`, which is what `Model::bit(v)` reads.
            let vars: Vec<Lit> = (0..nvars).map(|v| cnf.input_bit(0, v)).collect();
            for c in &clauses {
                let lits: Vec<Lit> = c
                    .iter()
                    .map(|&l| {
                        let base = vars[(l >> 1) as usize];
                        if l & 1 == 1 {
                            base.not()
                        } else {
                            base
                        }
                    })
                    .collect();
                cnf.add_clause(&lits);
            }
            cnf.true_lit()
        });

        match got {
            Sat::Unknown => continue, // honest, and the caps are far away here
            Sat::Sat => {
                sat_seen += 1;
                assert!(expect, "trial {trial}: claimed Sat for an unsatisfiable CNF");
                // The model must actually satisfy every clause.
                for (i, c) in clauses.iter().enumerate() {
                    let ok = c.iter().any(|&l| {
                        let v = l >> 1;
                        let sign = l & 1 == 1;
                        let bit = model.bit(v).unwrap_or(false);
                        bit != sign
                    });
                    assert!(ok, "trial {trial}: model does not satisfy clause {i}");
                }
            }
            Sat::Unsat => {
                unsat_seen += 1;
                if expect {
                    let mut txt = String::new();
                    for c in &clauses {
                        txt.push_str("  (");
                        for (i, &l) in c.iter().enumerate() {
                            if i > 0 { txt.push_str(" | "); }
                            if l & 1 == 1 { txt.push('!'); }
                            txt.push_str(&format!("x{}", l >> 1));
                        }
                        txt.push_str(")\n");
                    }
                    panic!("trial {trial}: claimed Unsat for a satisfiable CNF (nvars={nvars}):\n{txt}");
                }
            }
        }
    }
    assert!(sat_seen > 100, "expected a healthy share of SAT cases, got {sat_seen}");
    assert!(unsat_seen > 100, "expected a healthy share of UNSAT cases, got {unsat_seen}");
}
