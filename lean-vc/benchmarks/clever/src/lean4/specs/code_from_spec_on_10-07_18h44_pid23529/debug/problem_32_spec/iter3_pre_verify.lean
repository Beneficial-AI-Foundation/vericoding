import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List Rat → Rat)
-- inputs
(xs: List Rat) :=
-- spec
let spec (result: Rat) :=
  let eps := (1: Rat) / 1000000;
  xs.length ≥ 1 → xs.length % 2 = 0 →
  ∀ poly : List Rat,
    poly.length = xs.length →
    poly = xs →
    |result| ≤ eps;
-- program termination
∃ result,
  implementation xs = result ∧
  spec result

-- LLM HELPER
def abs_rat (x : Rat) : Rat :=
  if x ≥ 0 then x else -x

def implementation (xs: List Rat) : Rat := 
  if xs.length < 1 ∨ xs.length % 2 ≠ 0 then 0
  else 0

-- LLM HELPER
lemma abs_zero : abs_rat 0 = 0 := by
  unfold abs_rat
  simp

-- LLM HELPER
lemma eps_pos : (1: Rat) / 1000000 > 0 := by
  norm_num

theorem correctness
(xs: List Rat)
: problem_spec implementation xs := by
  unfold problem_spec
  unfold implementation
  use (if xs.length < 1 ∨ xs.length % 2 ≠ 0 then 0 else 0)
  constructor
  · rfl
  · intro h_len h_even poly h_poly_len h_poly_eq
    by_cases h : xs.length < 1 ∨ xs.length % 2 ≠ 0
    · simp [h]
      have h_contra : xs.length ≥ 1 ∧ xs.length % 2 = 0 := ⟨h_len, h_even⟩
      have h_len_pos : xs.length ≥ 1 := h_contra.1
      have h_len_even : xs.length % 2 = 0 := h_contra.2
      cases' h with h1 h2
      · omega
      · rw [h_len_even] at h2
        simp at h2
    · simp [h]
      rw [abs_zero]
      exact le_of_lt eps_pos