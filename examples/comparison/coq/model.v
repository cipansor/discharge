(* The model the positive fixture and both negative fixtures import, so the
   teeth test the code and not a second, drifting transcription of the model. *)
Require Import ZArith.
Open Scope Z_scope.

Definition MAX : Z := 65535.

(* A u16 add, modelled WITH the 2^16 wrap. Modelling the wrap is the whole
   point: without it the model would be mathematical integers, not the
   machine's function, and the swapped-branch bug below would be provable. *)
Definition add_eng (a b : Z) : Z := Z.modulo (a + b) 65536.

Definition sat_add (a b : Z) : Z :=
  if Z.gtb a (MAX - b) then MAX else add_eng a b.

Definition clamp (x lo hi : Z) : Z :=
  if Z.ltb x lo then lo else if Z.gtb x hi then hi else x.

Fixpoint sum_to (n : nat) : nat :=
  match n with O => O | S k => S (sum_to k) end.
