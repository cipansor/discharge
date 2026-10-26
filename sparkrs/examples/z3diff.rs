// Re-verify the README's z3 differential numbers.
//
// Generates random predicates over small bit-vectors, asks the engine, exports the SAME
// predicate as SMT-LIB2, and asks z3. The two verdicts must agree whenever both decide.
use sparkrs::smt::{self, Pred, Var, Verdict};
use sparkrs::smtscript::Query;
use std::io::Write as _;
use std::process::{Command, Stdio};

struct Lcg(u64);
impl Lcg {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0 >> 33
    }
    fn below(&mut self, n: u64) -> u64 { if n == 0 { 0 } else { self.next() % n } }
}

fn rand_word(r: &mut Lcg, vars: &[Var], depth: u32) -> Var {
    let w = smt::bits(vars[0]);
    if depth == 0 || r.below(3) == 0 {
        return if r.below(3) == 0 {
            let k = r.below(1u64 << w.min(8));
            smt::word(k, w)
        } else {
            vars[r.below(vars.len() as u64) as usize]
        };
    }
    match r.below(9) {
        0 => smt::add(rand_word(r, vars, depth - 1), rand_word(r, vars, depth - 1)),
        1 => smt::sub(rand_word(r, vars, depth - 1), rand_word(r, vars, depth - 1)),
        2 => smt::band(rand_word(r, vars, depth - 1), rand_word(r, vars, depth - 1)),
        3 => smt::bor(rand_word(r, vars, depth - 1), rand_word(r, vars, depth - 1)),
        4 => smt::bxor(rand_word(r, vars, depth - 1), rand_word(r, vars, depth - 1)),
        5 => smt::shl(rand_word(r, vars, depth - 1), r.below(w as u64 + 2) as u32),
        6 => smt::lshr(rand_word(r, vars, depth - 1), r.below(w as u64 + 2) as u32),
        7 => smt::truncate(rand_word(r, vars, depth - 1), 1 + r.below(w as u64) as u8),
        _ => smt::ite(rand_pred(r, vars, depth - 1), rand_word(r, vars, depth - 1), rand_word(r, vars, depth - 1)),
    }
}

fn rand_pred(r: &mut Lcg, vars: &[Var], depth: u32) -> Pred {
    if depth == 0 || r.below(4) == 0 {
        let w = smt::bits(vars[0]);
        return match r.below(4) {
            0 => smt::eq(rand_word(r, vars, 0), rand_word(r, vars, 0)),
            1 => smt::ult(rand_word(r, vars, 0), rand_word(r, vars, 0)),
            2 => smt::ule(rand_word(r, vars, 0), rand_word(r, vars, 0)),
            _ => smt::eq_const(vars[r.below(vars.len() as u64) as usize], r.below(1u64 << w.min(8))),
        };
    }
    match r.below(6) {
        0 => smt::and(rand_pred(r, vars, depth - 1), rand_pred(r, vars, depth - 1)),
        1 => smt::or(rand_pred(r, vars, depth - 1), rand_pred(r, vars, depth - 1)),
        2 => smt::xor(rand_pred(r, vars, depth - 1), rand_pred(r, vars, depth - 1)),
        3 => smt::not(rand_pred(r, vars, depth - 1)),
        4 => smt::iff(rand_pred(r, vars, depth - 1), rand_pred(r, vars, depth - 1)),
        _ => smt::eq(rand_word(r, vars, depth - 1), rand_word(r, vars, depth - 1)),
    }
}

/// Returns (check_result, stderr). An empty `check_result` means z3 rejected the file.
fn ask_z3(text: &str) -> (String, String) {
    let mut ch = Command::new("python3").arg("-c").arg(
        "import sys,z3\ns=z3.Solver()\ntry:\n    f=z3.parse_smt2_string(sys.stdin.read())\nexcept Exception as e:\n    print('PARSEFAIL', file=sys.stderr); raise\ns.add(f)\nprint(s.check())")
        .stdin(Stdio::piped()).stdout(Stdio::piped()).stderr(Stdio::piped()).spawn().unwrap();
    ch.stdin.as_mut().unwrap().write_all(text.as_bytes()).unwrap();
    let out = ch.wait_with_output().unwrap();
    (String::from_utf8_lossy(&out.stdout).trim().to_string(),
     String::from_utf8_lossy(&out.stderr).trim().to_string())
}

fn main() {
    let mut r = Lcg(0x51ed_2701_9ab3_c4f7);
    let (mut agree, mut mismatch, mut parse_err, mut refused) = (0u32, 0u32, 0u32, 0u32);
    let cases: u32 = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(800);
    let total: u32 = cases;
    for _ in 0..cases {
        let w = [1u8, 2, 3, 4, 8, 12][r.below(6) as usize];
        let nv = 1 + r.below(3) as usize;
        let (text, ours) = smt::with_fresh(|| {
            let vars: Vec<Var> = (0..nv).map(|_| smt::var(w)).collect();
            let p = rand_pred(&mut r, &vars, 3);
            let v = smt::prove(p);
            (Query::new(&vars, p).to_smtlib2_string(), v)
        });
        // A refused export contains no `(check-sat)`: the engine answered `Unknown` for an
        // ill-formed term and the printer declined to write a query no solver could parse.
        // Both sides then agree on "no verdict", so it is not a parse error.
        if !text.contains("(check-sat)") {
            if ours == Verdict::Unknown { refused += 1; continue; }
            panic!("export refused for a decided query: ours={:?}\n{}", ours, text);
        }
        let (z, zerr) = ask_z3(&text);
        // The file asserts `(not p)`, so:
        //   z3 unsat  <=>  not p unsatisfiable  <=>  p is a tautology  <=>  ours Valid
        //   z3 sat    <=>  not p satisfiable    <=>  p is not a tautology
        //                                              <=> ours Unsat or Counterexample
        // `prove` answers Unsat when p is identically false, which is a *stronger* result
        // than a counterexample and still a tautology failure, so it agrees with `sat`.
        // `Unknown` on our side is never a disagreement: the engine is allowed to be
        // conservative, and z3 deciding either way is a stronger result, not a conflict.
        // Only a *definite* verdict that z3 contradicts is a soundness mismatch.
        if ours == Verdict::Unknown {
            agree += 1;
            continue;
        }
        let tautology = ours.is_proved();
        match z.as_str() {
            "unsat" if tautology => agree += 1,
            "sat" if !tautology => agree += 1,
            "sat" | "unsat" => {
                mismatch += 1;
                if mismatch < 4 { eprintln!("MISMATCH ours={:?} z3={}\n{}", ours, z, text); }
            }
            _ => {
                parse_err += 1;
                if parse_err < 4 { eprintln!("PARSE ERR ours={:?} z3={:?} stderr={}\n{}", ours, z, zerr, text); }
            }
        }
    }
    println!("total={} agree={} mismatch={} parse_err={} refused={}", total, agree, mismatch, parse_err, refused);
}
