/-
  The swapped-branch bug: the guarded add is the one that can overflow. The
  claim is the positive fixture's, and the script takes the same steps for the
  correct and the swapped definition, so what fails is a genuine unprovable
  goal and not a tactic aimed at the wrong branch: with the definition
  corrected, this file compiles. One false claim per file, so each rejection is
  evidence about its own claim.
-/
import model

def satAddBuggy (a b : Nat) : Nat :=
  if a > MAX - b then addEng a b else MAX

theorem satAddBuggy_spec (a b : Nat) (_ha : a ≤ MAX) (_hb : b ≤ MAX) :
    (a ≤ MAX - b → satAddBuggy a b = a + b) ∧
    (a > MAX - b → satAddBuggy a b = MAX) := by
  unfold satAddBuggy MAX at *
  constructor <;> intro h
  · rw [ite_eq_right (by omega)]
    try (unfold addEng; rw [Nat.mod_eq_of_lt (by omega)])
    try omega
  · rw [ite_eq_left (by omega)]
    try (unfold addEng; rw [Nat.mod_eq_of_lt (by omega)])
    try omega
