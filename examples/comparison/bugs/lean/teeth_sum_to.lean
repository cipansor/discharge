/-
  The wrong-loop-body bug: the recursion adds two, so the invariant is not
  preserved. The script supplies the induction hypothesis its premise, so it
  takes the same steps for the correct and the buggy definition, and with the
  definition corrected this file compiles. Its own file, for the same reason as
  the other.
-/
import model

def sumToBuggy : Nat → Nat
  | 0 => 0
  | n + 1 => sumToBuggy n + 2

theorem sumToBuggy_id (n : Nat) (h : n ≤ 8) : sumToBuggy n = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp [sumToBuggy, ih (by omega)]
