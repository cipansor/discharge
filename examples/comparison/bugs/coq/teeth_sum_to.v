(* The wrong-loop-body bug: the recursion adds two, so the invariant is not
   preserved. Its own compilation unit, for the same reason as the other. *)
Require Import ZArith.
Require Import model.

Fixpoint sum_to_buggy (n : nat) : nat :=
  match n with O => O | S k => S (S (sum_to_buggy k)) end.

Theorem sum_to_buggy_id : forall n, sum_to_buggy n = n.
Proof. induction n as [| k IH]; simpl; auto. Qed.
