/- 
function_signature: "def any_int(a: float, b: float, c: float) -> bool"
docstring: |
    Create a function that takes 3 numbers.
    Returns true if one of the numbers is equal to the sum of the other two, and all numbers are integers.
    Returns false in any other cases.
test_cases:
  - input: [5, 2, 7]
    expected_output: true
  - input: [3, 2, 2]
    expected_output: false
  - input: [3, -2, 1]
    expected_output: true
  - input: [3.6, -2.2, 2]
    expected_output: false
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def is_integer (x : Rat) : Bool :=
  x.den = 1

def implementation (a: Rat) (b: Rat) (c: Rat) : Bool :=
  is_integer a && is_integer b && is_integer c && 
  (a + b = c || a + c = b || b + c = a)

def problem_spec
-- function signature
(implementation: Rat → Rat → Rat → Bool)
-- inputs
(a: Rat) (b: Rat) (c: Rat) :=
-- spec
let spec (result : Bool) :=
  let nums := [a, b, c];
  result = true ↔ ∃ i j k : ℕ, {i, j, k} ⊆ ({0, 1, 2} : Set ℕ) ∧ i ≠ j ∧ j ≠ k ∧ k ≠ i ∧ (nums[i]! + nums[j]! = nums[k]!) ∧ a.den = 1 ∧ a.den = b.den ∧ a.den = c.den
-- program termination
∃ result,
  implementation a b c = result ∧
  spec result

-- LLM HELPER
lemma all_integers_condition (a b c : Rat) :
  (a.den = 1 ∧ a.den = b.den ∧ a.den = c.den) ↔ (a.den = 1 ∧ b.den = 1 ∧ c.den = 1) := by
  constructor
  · intro h
    exact ⟨h.1, h.2.1 ▸ h.1, h.2.2 ▸ h.1⟩
  · intro h
    exact ⟨h.1, h.2.1 ▸ h.1, h.2.2.symm ▸ h.1⟩

-- LLM HELPER  
lemma sum_condition_equiv (a b c : Rat) :
  (∃ i j k : ℕ, {i, j, k} ⊆ ({0, 1, 2} : Set ℕ) ∧ i ≠ j ∧ j ≠ k ∧ k ≠ i ∧ ([a, b, c][i]! + [a, b, c][j]! = [a, b, c][k]!)) ↔ 
  (a + b = c ∨ a + c = b ∨ b + c = a) := by
  constructor
  · intro ⟨i, j, k, _, hij, hjk, hki, hsum⟩
    by_cases h1 : i = 0
    · by_cases h2 : j = 1
      · have hk : k = 2 := by
          have : k ∈ ({0, 1, 2} : Set ℕ) := by simp
          have : k ≠ 0 := h1 ▸ hki.symm
          have : k ≠ 1 := h2 ▸ hjk.symm
          omega
        simp [h1, h2, hk] at hsum
        right; right; exact hsum
      · by_cases h3 : j = 2
        · have hk : k = 1 := by
            have : k ∈ ({0, 1, 2} : Set ℕ) := by simp
            have : k ≠ 0 := h1 ▸ hki.symm
            have : k ≠ 2 := h3 ▸ hjk.symm
            omega
          simp [h1, h3, hk] at hsum
          right; left; exact hsum
        · have : j = 0 ∨ j = 1 ∨ j = 2 := by simp
          simp [h2, h3] at this
          have : j = 0 := this
          exact (hij (h1 ▸ this)).elim
    · by_cases h2 : i = 1
      · by_cases h3 : j = 0
        · have hk : k = 2 := by
            have : k ∈ ({0, 1, 2} : Set ℕ) := by simp
            have : k ≠ 1 := h2 ▸ hki.symm
            have : k ≠ 0 := h3 ▸ hjk.symm
            omega
          simp [h2, h3, hk] at hsum
          right; right; exact hsum
        · by_cases h4 : j = 2
          · have hk : k = 0 := by
              have : k ∈ ({0, 1, 2} : Set ℕ) := by simp
              have : k ≠ 1 := h2 ▸ hki.symm
              have : k ≠ 2 := h4 ▸ hjk.symm
              omega
            simp [h2, h4, hk] at hsum
            left; exact hsum
          · have : j = 0 ∨ j = 1 ∨ j = 2 := by simp
            simp [h3, h4] at this
            have : j = 1 := this
            exact (hij (h2 ▸ this)).elim
      · have : i = 2 := by
          have : i ∈ ({0, 1, 2} : Set ℕ) := by simp
          omega
        by_cases h3 : j = 0
        · have hk : k = 1 := by
            have : k ∈ ({0, 1, 2} : Set ℕ) := by simp
            have : k ≠ 2 := this ▸ hki.symm
            have : k ≠ 0 := h3 ▸ hjk.symm
            omega
          simp [this, h3, hk] at hsum
          right; left; exact hsum
        · by_cases h4 : j = 1
          · have hk : k = 0 := by
              have : k ∈ ({0, 1, 2} : Set ℕ) := by simp
              have : k ≠ 2 := this ▸ hki.symm
              have : k ≠ 1 := h4 ▸ hjk.symm
              omega
            simp [this, h4, hk] at hsum
            left; exact hsum
          · have : j = 0 ∨ j = 1 ∨ j = 2 := by simp
            simp [h3, h4] at this
            have : j = 2 := this
            exact (hij (this.symm ▸ this)).elim
  · intro h
    cases h with
    | inl h => exact ⟨0, 1, 2, by simp, by simp, by simp, by simp, by simp [h]⟩
    | inr h => cases h with
      | inl h => exact ⟨0, 2, 1, by simp, by simp, by simp, by simp, by simp [h]⟩
      | inr h => exact ⟨1, 2, 0, by simp, by simp, by simp, by simp, by simp [h]⟩

theorem correctness
(a: Rat) (b: Rat) (c: Rat)
: problem_spec implementation a b c := by
  simp [problem_spec]
  use implementation a b c
  constructor
  · rfl
  · simp [implementation, is_integer]
    rw [all_integers_condition, sum_condition_equiv]
    constructor
    · intro h
      exact ⟨h.2, ⟨h.1.1, h.1.2.1, h.1.2.2⟩⟩
    · intro ⟨h1, h2⟩
      exact ⟨⟨h2.1, h2.2.1, h2.2.2⟩, h1⟩

-- #test implementation 5 2 7 = true
-- #test implementation 3 2 2 = false
-- #test implementation 3 (-2) 1 = true
-- #test implementation 3.6 (-2.2) 2 = false