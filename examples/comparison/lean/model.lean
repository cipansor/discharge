/-
  The model the positive fixture and both negative fixtures import, so the
  teeth test the code and not a second, drifting transcription of the model.
  As in Coq, the u16 wrap is modelled explicitly: without it the model would be
  mathematical integers, not the machine's function, and the swapped-branch bug
  below would be provable.
-/

def MAX : Nat := 65535

def addEng (a b : Nat) : Nat := (a + b) % 65536

def satAdd (a b : Nat) : Nat :=
  if a > MAX - b then MAX else addEng a b

def clamp (x lo hi : Nat) : Nat :=
  if x < lo then lo else if x > hi then hi else x

def sumTo : Nat → Nat
  | 0 => 0
  | n + 1 => sumTo n + 1
