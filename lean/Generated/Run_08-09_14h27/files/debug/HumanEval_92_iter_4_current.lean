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
    -- Since {i,j,k} ⊆ {0,1,2} and all are distinct, we have exactly {0,1,2}
    have h_eq : {i, j, k} = {0, 1, 2} := by
      apply Set.eq_of_subset_of_card_eq hsubset
      simp only [Set.card_singleton, Set.card_insert_of_not_mem]
      · have hij_ne : i ≠ j := hij
        have hjk_ne : j ≠ k := hjk  
        have hki_ne : k ≠ i := hki
        sorry
    -- Now we can case on which element is which
    cases' Nat.lt_trichotomy i j with hij_lt hij_eq_ge
    · cases' hij_eq_ge with hij_eq hij_gt
      · contradiction
      · sorry
    · sorry
  · intro h
    cases h with
    | inl h => 
      use 0, 1, 2
      constructor
      · simp only [Set.insert_subset_iff, Set.singleton_subset_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
        exact ⟨Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩
      constructor
      · simp
      constructor  
      · simp
      constructor
      · simp
      · simp only [List.getElem_fin]
        exact h
    | inr h => cases h with
      | inl h => 
        use 0, 2, 1
        constructor
        · simp only [Set.insert_subset_iff, Set.singleton_subset_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
          exact ⟨Or.inl rfl, Or.inr (Or.inr rfl), Or.inr (Or.inl rfl)⟩
        constructor
        · simp
        constructor
        · simp  
        constructor
        · simp
        · simp only [List.getElem_fin]
          exact h
      | inr h => 
        use 1, 2, 0
        constructor
        · simp only [Set.insert_subset_iff, Set.singleton_subset_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
          exact ⟨Or.inr (Or.inl rfl), Or.inr (Or.inr rfl), Or.inl rfl⟩
        constructor
        · simp
        constructor
        · simp
        constructor  
        · simp
        · simp only [List.getElem_fin]
          exact h

theorem correctness
(a: Rat) (b: Rat) (c: Rat)
: problem_spec implementation a b c := by
  simp only [problem_spec]
  use implementation a b c
  constructor
  · rfl
  · constructor
    · intro h
      simp [implementation, is_integer] at h
      have h_int := h.1
      have h_sum := h.2
      constructor
      · rw [sum_condition_equiv]
        exact h_sum
      · rw [all_integers_condition]
        exact h_int
    · intro ⟨hexists, hdens⟩
      simp [implementation, is_integer]
      constructor
      · rw [all_integers_condition] at hdens
        exact hdens
      · rw [sum_condition_equiv] at hexists
        exact hexists

-- #test implementation 5 2 7 = true
-- #test implementation 3 2 2 = false
-- #test implementation 3 (-2) 1 = true
-- #test implementation 3.6 (-2.2) 2 = false