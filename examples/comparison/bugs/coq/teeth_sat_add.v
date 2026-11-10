(* The swapped-branch bug: the guarded add is the one that can overflow. The
   claim is the positive fixture's; the script is written so it does not assume
   the definition's shape, so what fails is a genuine unprovable goal and not a
   tactic aimed at the wrong branch. Correcting the definition makes this file
   compile, which is what shows the rejection is of the swap. One false theorem
   per compilation unit, because `coqc` stops at the first failed proof. *)
Require Import ZArith.
Require Import Lia.
Require Import model.
Open Scope Z_scope.

Definition sat_add_buggy (a b : Z) : Z :=
  if Z.gtb a (MAX - b) then add_eng a b else MAX.

Theorem sat_add_buggy_spec :
  forall a b, 0 <= a <= MAX -> 0 <= b <= MAX ->
    (a <= MAX - b -> sat_add_buggy a b = a + b) /\
    (a >  MAX - b -> sat_add_buggy a b = MAX).
Proof.
  intros a b Ha Hb. unfold sat_add_buggy, add_eng, MAX in *. split; intros H;
    destruct (Z.gtb a (65535 - b)) eqn:E;
    try (apply Z.gtb_lt in E);
    try (rewrite Z.gtb_ltb in E; apply Z.ltb_ge in E);
    try (rewrite Z.mod_small by lia);
    lia.
Qed.
