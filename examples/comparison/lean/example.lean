/-
  The three functions, with the full contracts: `satAdd` says the result is the
  sum when it fits and MAX when it does not, so `always return MAX` fails;
  `clamp` says which arm is taken, so `always return lo` fails. Only Lean core
  is used (no Mathlib), so each `if` is rewritten by its guard with
  `ite_eq_left` / `ite_eq_right` rather than by a `split_ifs` tactic.
-/
import model

-- `ha` and `hb` are the real domain (both operands fit in a `u16`). They are
-- not needed for the proof, because Lean's `Nat` subtraction is truncated, but
-- they state the range the machine function is defined on.
theorem satAdd_spec (a b : Nat) (_ha : a ≤ MAX) (_hb : b ≤ MAX) :
    (a ≤ MAX - b → satAdd a b = a + b) ∧
    (a > MAX - b → satAdd a b = MAX) := by
  unfold satAdd addEng MAX at *
  constructor <;> intro h
  · rw [ite_eq_right (by omega)]
    rw [Nat.mod_eq_of_lt (by omega)]
  · rw [ite_eq_left h]

theorem clamp_spec (x lo hi : Nat) (_hlo : lo ≤ hi) :
    (x < lo → clamp x lo hi = lo) ∧
    (lo ≤ x → x > hi → clamp x lo hi = hi) ∧
    (lo ≤ x → x ≤ hi → clamp x lo hi = x) := by
  unfold clamp
  constructor
  · intro h; rw [ite_eq_left h]
  constructor <;> intro h1 h2
  · rw [ite_eq_right (by omega), ite_eq_left h2]
  · rw [ite_eq_right (by omega), ite_eq_right (by omega)]

theorem sumTo_id (n : Nat) : sumTo n = n := by
  induction n with
  | zero => rfl
  | succ k ih => simp [sumTo, ih]
