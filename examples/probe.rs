// Measure the scaling wall: at what width/op does the engine give up?
//
// `UNKNOWN` means neither engine decided the query. The BDD engine is tried first and the
// SAT engine takes over when the BDD arena fills, so a row that is `valid` at a width the
// BDD engine alone cannot reach is the SAT engine earning its place -- for example
// `add_comm 64b`, which is `UNKNOWN` with the fallback disabled and `valid` with it.
//
// Run with `--release`; the debug build is ~10x slower and will hit the conflict budget.
use discharge::smt::{self, var, Verdict};

fn t(label: &str, f: impl FnOnce() -> Verdict) {
    let start = std::time::Instant::now();
    let v = smt::with_fresh(|| { let r = f(); (r, smt::node_count()) });
    let ms = start.elapsed().as_millis();
    let kind = match v.0 { Verdict::Valid => "valid", Verdict::Unsat => "unsat", Verdict::Counterexample(_) => "cex", Verdict::Unknown => "UNKNOWN" };
    println!("{label:44} {kind:8} nodes={:6} {ms:5}ms", v.1);
}

fn main() {
    for w in [4u8, 6, 8, 10, 12, 16] {
        t(&format!("mul_comm {w}b"), || { let a = var(w); let b = var(w); smt::prove(smt::eq(smt::mul(a,b), smt::mul(b,a))) });
    }
    for w in [4u8, 8, 12, 16, 24, 32] {
        t(&format!("add_assoc {w}b"), || { let a = var(w); let b = var(w); let c = var(w);
            smt::prove(smt::eq(smt::add(smt::add(a,b),c), smt::add(a,smt::add(b,c)))) });
    }
    for w in [8u8, 16, 32] {
        t(&format!("sub_comm-false {w}b"), || { let a = var(w); let b = var(w); smt::prove(smt::eq(smt::sub(a,b), smt::sub(b,a))) });
    }
    // Ripple-carry adder equivalence: past the BDD wall, inside the SAT engine's reach.
    for w in [24u8, 32, 48, 64] {
        t(&format!("add_comm {w}b"), || { let a = var(w); let b = var(w); smt::prove(smt::eq(smt::add(a,b), smt::add(b,a))) });
    }
}
