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
  · intro ⟨i, j, k, hsubset, hij, hjk, hki, hsum⟩
    have hi_mem : i ∈ ({0, 1, 2} : Set ℕ) := by
      simp at hsubset
      exact hsubset.1
    have hj_mem : j ∈ ({0, 1, 2} : Set ℕ) := by
      simp at hsubset
      exact hsubset.2.1
    have hk_mem : k ∈ ({0, 1, 2} : Set ℕ) := by
      simp at hsubset
      exact hsubset.2.2
    interval_cases i
    · interval_cases j
      · contradiction
      · interval_cases k
        · exact (hki rfl).elim
        · exact (hjk rfl).elim
        · simp at hsum; right; right; exact hsum
      · interval_cases k
        · exact (hki rfl).elim
        · simp at hsum; right; left; exact hsum
        · exact (hjk rfl).elim
    · interval_cases j
      · interval_cases k
        · exact (hjk rfl).elim
        · exact (hki rfl).elim
        · simp at hsum; right; right; exact hsum
      · contradiction
      · interval_cases k
        · simp at hsum; left; exact hsum
        · exact (hki rfl).elim
        · exact (hjk rfl).elim
    · interval_cases j
      · interval_cases k
        · exact (hjk rfl).elim
        · simp at hsum; right; left; exact hsum
        · exact (hki rfl).elim
      · interval_cases k
        · simp at hsum; left; exact hsum
        · exact (hjk rfl).elim
        · exact (hki rfl).elim
      · contradiction
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