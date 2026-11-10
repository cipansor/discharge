Require Import ZArith.
Require Import Lia.
Require Import model.
Open Scope Z_scope.

(* The full saturation contract, not just a lower bound: the result IS the sum
   when it fits and IS MAX when it does not, so `always return MAX` fails. *)
Theorem sat_add_spec :
  forall a b, 0 <= a <= MAX -> 0 <= b <= MAX ->
    (a <= MAX - b -> sat_add a b = a + b) /\
    (a >  MAX - b -> sat_add a b = MAX).
Proof.
  intros a b Ha Hb. unfold sat_add, MAX in *. split; intros H.
  - destruct (Z.gtb a (65535 - b)) eqn:E.
    + apply Z.gtb_lt in E. lia.
    + unfold add_eng. rewrite Z.mod_small by lia. lia.
  - destruct (Z.gtb a (65535 - b)) eqn:E.
    + reflexivity.
    + rewrite Z.gtb_ltb in E. apply Z.ltb_ge in E. lia.
Qed.

(* The full clamp contract: which arm is taken, not only that the result is in
   range, so `always return lo` fails. *)
Theorem clamp_spec :
  forall x lo hi, lo <= hi ->
    (x < lo -> clamp x lo hi = lo) /\
    (lo <= x -> x > hi -> clamp x lo hi = hi) /\
    (lo <= x -> x <= hi -> clamp x lo hi = x).
Proof.
  intros x lo hi Hlo. unfold clamp. split; [| split]; intros.
  - destruct (Z.ltb x lo) eqn:E.
    + reflexivity.
    + apply Z.ltb_ge in E. lia.
  - destruct (Z.ltb x lo) eqn:E1.
    + apply Z.ltb_lt in E1. lia.
    + destruct (Z.gtb x hi) eqn:E2.
      * reflexivity.
      * rewrite Z.gtb_ltb in E2. apply Z.ltb_ge in E2. lia.
  - destruct (Z.ltb x lo) eqn:E1.
    + apply Z.ltb_lt in E1. lia.
    + destruct (Z.gtb x hi) eqn:E2.
      * apply Z.gtb_lt in E2. lia.
      * reflexivity.
Qed.

Theorem sum_to_id : forall n, sum_to n = n.
Proof. induction n as [| k IH]; simpl; auto. Qed.
