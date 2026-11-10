(* Two false claims. `coqc` must reject this file, which is the point: the
   model is the same one `../coq/example.v` proves, so the difference is the
   code, not the encoding. *)

Require Import ZArith.
Require Import Lia.
Open Scope Z_scope.

Definition MAX : Z := 65535.
Definition add_eng (a b : Z) : Z := Z.modulo (a + b) 65536.

(* Bug 1: the branches are swapped, so the guarded add is the overflowing one. *)
Definition sat_add_buggy (a b : Z) : Z :=
  if Z.gtb a (MAX - b) then add_eng a b else MAX.

Theorem sat_add_buggy_ge :
  forall a b, 0 <= a <= MAX -> 0 <= b <= MAX -> sat_add_buggy a b >= a.
Proof.
  intros a b Ha Hb.
  unfold sat_add_buggy, MAX in *.
  destruct (Z.gtb a (65535 - b)) eqn:E.
  - apply Z.gtb_lt in E. unfold add_eng. lia.
  - rewrite Z.gtb_ltb in E. apply Z.ltb_ge in E. lia.
Qed.

(* Bug 2: the loop body adds 2, so the invariant is not preserved. *)
Fixpoint sum_to_buggy (n : nat) : nat :=
  match n with O => O | S k => sum_to_buggy k + 2 end.

Theorem sum_to_buggy_id : forall n, n <= 8 -> sum_to_buggy n = n.
Proof.
  induction n as [| k IH]; simpl; intros H; auto.
  lia.
Qed.
