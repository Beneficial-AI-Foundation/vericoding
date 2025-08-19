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
  unfold problem_spec
  use implementation a h
  constructor
  · rfl
  · unfold implementation
    intro _
    split_ifs with ha
    · exact ha
    · constructor
      · intro h_contra
        contradiction
      · intro h_ne_zero
        simp only [mul_div_assoc, div_mul_cancel]
        exact h_ne_zero