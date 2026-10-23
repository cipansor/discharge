use sparkrs::smt::*;

#[test]
fn commutativity_of_add_is_proved() {
    with_fresh(|| {
        let x = var(8);
        let y = var(8);
        // x + y == y + x, both sides built as words then compared
        let lhs = add(x, y);
        let rhs = add(y, x);
        let p = eq(lhs, rhs);
        let v = prove(p);
        assert!(v.is_proved(), "expected proof, got {}", v);
    });
}

#[test]
fn bound_is_refuted_with_counterexample() {
    with_fresh(|| {
        let x = var(8);
        let v = prove(ule_const(x, 100));
        match v {
            Verdict::Counterexample(c) => {
                let xv = c.value_of(0).expect("x in model");
                assert!(xv > 100);
            }
            other => panic!("expected refutation, got {}", other),
        }
    });
}

#[test]
fn x_minus_x_is_zero() {
    with_fresh(|| {
        let x = var(16);
        let z = word(0, 16);
        let v = prove(eq(sub(x, x), z));
        assert!(v.is_proved(), "got {}", v);
    });
}

#[test]
fn mask_identity() {
    with_fresh(|| {
        let x = var(32);
        // (x & 0xFF) == (x % 256)
        let m = word(0xFF, 32);
        let lhs = band(x, m);
        let rhs = word(256, 32);
        // x & 0xFF < 256 always
        let v = prove(ult(lhs, rhs));
        assert!(v.is_proved(), "got {}", v);
    });
}
