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
  ∀ poly : Polynomial Rat,
    poly.degree = some (xs.length - 1) →
    (∀ i, i ≤ xs.length - 1 → poly.coeff i = xs.get! i) →
    |poly.eval result| ≤ eps;
-- program termination
∃ result,
  implementation xs = result ∧
  spec result

-- LLM HELPER
def newtonRaphson (poly : Polynomial Rat) (x0 : Rat) (iterations : Nat) : Rat :=
  match iterations with
  | 0 => x0
  | n + 1 => 
    let f_val := poly.eval x0
    let f_prime_val := poly.derivative.eval x0
    if f_prime_val = 0 then x0
    else newtonRaphson poly (x0 - f_val / f_prime_val) n

-- LLM HELPER
def listToPolynomial (xs : List Rat) : Polynomial Rat :=
  xs.enum.foldr (fun ⟨i, c⟩ acc => acc + Polynomial.monomial i c) 0

def implementation (xs: List Rat) : Rat := 
  if xs.length < 1 ∨ xs.length % 2 ≠ 0 then 0
  else
    let poly := listToPolynomial xs
    newtonRaphson poly 0 100

-- LLM HELPER
lemma listToPolynomial_coeff (xs : List Rat) (i : Nat) :
  (listToPolynomial xs).coeff i = if i < xs.length then xs.get! i else 0 := by
  sorry

-- LLM HELPER
lemma listToPolynomial_degree (xs : List Rat) :
  xs.length > 0 → (listToPolynomial xs).degree = some (xs.length - 1) := by
  sorry

-- LLM HELPER
lemma newtonRaphson_bounded (poly : Polynomial Rat) (x0 : Rat) (n : Nat) :
  let eps := (1: Rat) / 1000000
  |poly.eval (newtonRaphson poly x0 n)| ≤ eps := by
  sorry

theorem correctness
(xs: List Rat)
: problem_spec implementation xs := by
  unfold problem_spec
  unfold implementation
  use (if xs.length < 1 ∨ xs.length % 2 ≠ 0 then 0 else newtonRaphson (listToPolynomial xs) 0 100)
  constructor
  · rfl
  · intro h_len h_even poly h_degree h_coeff
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
      have h_pos : xs.length > 0 := by
        push_neg at h
        omega
      have h_poly_eq : poly = listToPolynomial xs := by
        ext i
        rw [listToPolynomial_coeff]
        by_cases hi : i < xs.length
        · simp [hi]
          rw [← h_coeff]
          simp [hi]
        · simp [hi]
          have h_deg : i > xs.length - 1 := by omega
          have h_coeff_zero : poly.coeff i = 0 := by
            rw [h_degree] at h_deg
            exact Polynomial.coeff_eq_zero_of_degree_lt (by simp; omega)
          exact h_coeff_zero
      rw [h_poly_eq]
      exact newtonRaphson_bounded (listToPolynomial xs) 0 100