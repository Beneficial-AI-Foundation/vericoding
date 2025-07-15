import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
(implementation: Rat → Rat → Rat)
(a h: Rat) :=
let spec (result: Rat) :=
  a = 0 → result = 0 ∧
  (a ≠ 0 → (2 * result) / a = h);
∃ result, implementation a h = result ∧
spec result

def implementation (a h: Rat) : Rat := 
  if a = 0 then 0 else (a * h) / 2

theorem correctness
(a h : Rat)
: problem_spec implementation a h := by
  use implementation a h
  constructor
  · rfl
  · simp [implementation]
    by_cases ha : a = 0
    · intro h_eq
      simp [ha]
    · intro h_ne
      simp [ha]
      field_simp [ha]
      ring