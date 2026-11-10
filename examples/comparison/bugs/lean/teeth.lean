/-
  Two false claims. `lean` must reject this file. Only Lean core is used (no
  Mathlib), so `split_ifs` is unavailable and the case split is written by
  hand with `by_cases`.
-/

def MAX : Nat := 65535
def addEng (a b : Nat) : Nat := (a + b) % 65536

-- Bug 1: the branches are swapped.
def satAddBuggy (a b : Nat) : Nat :=
  if a > MAX - b then addEng a b else MAX

theorem satAddBuggy_ge (a b : Nat) (ha : a ≤ MAX) (hb : b ≤ MAX) :
    satAddBuggy a b ≥ a := by
  unfold satAddBuggy addEng MAX at *
  by_cases h : a > 65535 - b
  · rw [if_pos h]
    omega
  · rw [if_neg h]; omega

-- Bug 2: the loop body adds 2, so the invariant is not preserved.
def sumToBuggy : Nat → Nat
  | 0 => 0
  | n + 1 => sumToBuggy n + 2

theorem sumToBuggy_id (n : Nat) (h : n ≤ 8) : sumToBuggy n = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp [sumToBuggy, ih]
