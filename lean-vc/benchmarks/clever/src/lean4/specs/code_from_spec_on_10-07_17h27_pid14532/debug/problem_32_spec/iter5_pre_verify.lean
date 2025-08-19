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
  (∀ x ∈ xs, |x| ≤ eps) →
  ∀ poly : Polynomial Rat,
    poly.degree = some (xs.length - 1) →
    (∀ i, i ≤ xs.length - 1 → poly.coeff i = xs.get! i) →
    |poly.eval result| ≤ eps;
-- program termination
∃ result,
  implementation xs = result ∧
  spec result

def implementation (xs: List Rat) : Rat := 0

-- LLM HELPER
lemma polynomial_eval_zero_eq_constant_coeff (poly : Polynomial Rat) :
  poly.eval 0 = poly.coeff 0 := by
  simp [Polynomial.eval_zero]

-- LLM HELPER
lemma list_get_bang_mem_of_nonempty {α : Type*} [Inhabited α] (xs : List α) (i : Nat) 
  (h : xs.length > i) : xs.get! i ∈ xs := by
  have h_lt : i < xs.length := h
  rw [List.get!_eq_get _ h_lt]
  exact List.get_mem xs i

theorem correctness
(xs: List Rat)
: problem_spec implementation xs
:= by
  use 0
  constructor
  · rfl
  · intro h_len h_even h_bound poly h_deg h_coeff
    rw [polynomial_eval_zero_eq_constant_coeff]
    rw [h_coeff 0]
    · apply h_bound
      apply list_get_bang_mem_of_nonempty
      exact h_len
    · exact Nat.zero_le (xs.length - 1)