Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition MAX : Z := 65535.

(* A u16 add, modelled WITH the 2^16 wrap. Modelling the wrap is the whole
   point: without it the model would be mathematical integers, not the
   machine's function. *)
Definition add_eng (a b : Z) : Z := Z.modulo (a + b) 65536.

Definition sat_add (a b : Z) : Z :=
  if Z.gtb a (MAX - b) then MAX else add_eng a b.

Theorem sat_add_ge :
  forall a b, 0 <= a <= MAX -> 0 <= b <= MAX -> sat_add a b >= a /\ sat_add a b >= b.
Proof.
  intros a b Ha Hb.
  unfold sat_add, MAX in *.
  destruct (Z.gtb a (65535 - b)) eqn:E.
  - lia.
  - rewrite Z.gtb_ltb in E. apply Z.ltb_ge in E.
    unfold add_eng. rewrite Z.mod_small by lia. lia.
Qed.

Definition clamp (x lo hi : Z) : Z :=
  if Z.ltb x lo then lo else if Z.gtb x hi then hi else x.

Theorem clamp_range :
  forall x lo hi, lo <= hi -> lo <= clamp x lo hi <= hi.
Proof.
  intros x lo hi H.
  unfold clamp.
  destruct (Z.ltb x lo) eqn:E1.
  - apply Z.ltb_lt in E1. lia.
  - destruct (Z.gtb x hi) eqn:E2.
    + apply Z.gtb_lt in E2. lia.
    + rewrite Z.gtb_ltb in E2.
      apply Z.ltb_ge in E2. apply Z.ltb_ge in E1. lia.
Qed.

Fixpoint sum_to (n : nat) : nat :=
  match n with O => O | S k => S (sum_to k) end.

Theorem sum_to_id : forall n, sum_to n = n.
Proof. induction n as [| k IH]; simpl; auto. Qed.
