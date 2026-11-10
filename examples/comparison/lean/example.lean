/-
  The same three functions as the Coq and Rust examples, so the comparison is
  about the tools. As in Coq, the u16 wrap is modelled explicitly: without it
  the model would be mathematical integers, not the machine's function.
  Only Lean core is used (no Mathlib), so `split_ifs` is unavailable and the
  case split is written by hand with `by_cases`.
-/

def MAX : Nat := 65535

def addEng (a b : Nat) : Nat := (a + b) % 65536

def satAdd (a b : Nat) : Nat :=
  if a > MAX - b then MAX else addEng a b

theorem satAdd_ge (a b : Nat) (ha : a ≤ MAX) (hb : b ≤ MAX) :
    satAdd a b ≥ a ∧ satAdd a b ≥ b := by
  unfold satAdd addEng MAX at *
  by_cases h : a > 65535 - b
  · rw [if_pos h]; constructor <;> omega
  · rw [if_neg h]
    have hle : a + b ≤ 65535 := by omega
    rw [Nat.mod_eq_of_lt (by omega)]
    constructor <;> omega

def clamp (x lo hi : Nat) : Nat :=
  if x < lo then lo else if x > hi then hi else x

theorem clamp_range (x lo hi : Nat) (h : lo ≤ hi) :
    lo ≤ clamp x lo hi ∧ clamp x lo hi ≤ hi := by
  unfold clamp
  by_cases h1 : x < lo
  · rw [if_pos h1]; omega
  · rw [if_neg h1]
    by_cases h2 : x > hi
    · rw [if_pos h2]; omega
    · rw [if_neg h2]; omega

def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo n + 1

theorem sumTo_id (n : Nat) : sumTo n = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp [sumTo, ih]
