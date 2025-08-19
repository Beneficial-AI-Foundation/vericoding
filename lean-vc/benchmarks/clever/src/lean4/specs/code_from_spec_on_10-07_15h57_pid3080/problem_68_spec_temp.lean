import Mathlib
import Mathlib.Data.List.Basic
import Mathlib.Data.String.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Basic

def problem_spec
-- function signature
(implementation: List Nat → List Nat)
-- inputs
(numbers: List Nat) :=
-- spec
let spec (result: List Nat) :=
(result.length = 0 ↔ ∀ i, i < numbers.length → numbers[i]! % 2 = 1) ∧
(result.length = 2 ↔ ∃ i, i < numbers.length ∧
  numbers[i]! % 2 = 0 ∧
  result[0]! = numbers[i]! ∧
  result[1]! = i ∧
  (∀ j, j < numbers.length → j < i → (numbers[j]! % 2 = 1 ∨ numbers[i]! < numbers[j]!)) ∧
  (∀ k, k < numbers.length → numbers[k]! % 2 = 0 → numbers[i]! ≤ numbers[k]!));
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
def find_min_even_aux (numbers: List Nat) (i: Nat) (min_val: Nat) (min_idx: Nat) (found: Bool) : List Nat :=
if i ≥ numbers.length then
  if found then [min_val, min_idx] else []
else
  let curr := numbers[i]!
  if curr % 2 = 0 then
    if ¬found ∨ curr < min_val then
      find_min_even_aux numbers (i + 1) curr i true
    else
      find_min_even_aux numbers (i + 1) min_val min_idx found
  else
    find_min_even_aux numbers (i + 1) min_val min_idx found

def implementation (numbers: List Nat) : List Nat := 
  find_min_even_aux numbers 0 0 0 false

-- LLM HELPER  
lemma find_min_even_aux_terminates (numbers: List Nat) (i min_val min_idx: Nat) (found: Bool) :
  ∃ result, find_min_even_aux numbers i min_val min_idx found = result := by
  use find_min_even_aux numbers i min_val min_idx found
  rfl

-- LLM HELPER
lemma find_min_even_aux_spec (numbers: List Nat) (i min_val min_idx: Nat) (found: Bool) :
  let result := find_min_even_aux numbers i min_val min_idx found
  (result.length = 0 ∨ result.length = 2) := by
  unfold find_min_even_aux
  generalize h : numbers.length = n
  by_cases h1 : i ≥ numbers.length
  · simp [h1]
    by_cases h2 : found
    · simp [h2]
    · simp [h2]
  · simp [h1]
    by_cases h2 : numbers[i]! % 2 = 0
    · simp [h2]
      by_cases h3 : ¬found ∨ numbers[i]! < min_val
      · simp [h3]
        apply find_min_even_aux_spec
      · simp [h3]
        apply find_min_even_aux_spec
    · simp [h2]
      apply find_min_even_aux_spec

-- LLM HELPER
lemma implementation_length (numbers: List Nat) :
  let result := implementation numbers
  result.length = 0 ∨ result.length = 2 := by
  unfold implementation
  apply find_min_even_aux_spec

-- LLM HELPER
lemma implementation_correct_empty (numbers: List Nat) :
  implementation numbers = [] ↔ ∀ i, i < numbers.length → numbers[i]! % 2 = 1 := by
  constructor
  · intro h i hi
    unfold implementation at h
    by_contra h_contra
    have h_even : numbers[i]! % 2 = 0 := by
      cases Nat.mod_two_eq_zero_or_one (numbers[i]!) with
      | inl h_zero => exact h_zero
      | inr h_one => contradiction
    have h_exists : ∃ j, j < numbers.length ∧ numbers[j]! % 2 = 0 := ⟨i, hi, h_even⟩
    have h_nonnil : find_min_even_aux numbers 0 0 0 false ≠ [] := by
      induction' numbers.length using Nat.strong_induction_on with k ih
      cases k with
      | zero => 
        simp at hi
      | succ k' =>
        unfold find_min_even_aux
        simp
        by_cases h_case : 0 ≥ numbers.length
        · simp [h_case]
          simp at hi
          simp at h_case
          omega
        · simp [h_case]
          by_cases h_first : numbers[0]! % 2 = 0
          · simp [h_first]
            simp [Bool.not_false_eq_true]
            induction' k' using Nat.strong_induction_on with m ihm
            cases m with
            | zero =>
              unfold find_min_even_aux
              simp
              by_cases h_len : 1 ≥ numbers.length
              · simp [h_len]
              · simp [h_len]
                by_cases h_next : numbers[1]! % 2 = 0
                · simp [h_next]
                  by_cases h_comp : numbers[1]! < numbers[0]!
                  · simp [h_comp]
                    apply ihm
                    simp
                  · simp [h_comp]
                    apply ihm
                    simp
                · simp [h_next]
                  apply ihm
                  simp
            | succ m' =>
              apply ihm
              simp
          · simp [h_first]
            apply ih
            simp
    rw [h] at h_nonnil
    simp at h_nonnil
  · intro h
    unfold implementation
    induction' numbers.length using Nat.strong_induction_on with k ih
    cases k with
    | zero => 
      unfold find_min_even_aux
      simp
    | succ k' =>
      unfold find_min_even_aux
      simp
      by_cases h_case : 0 ≥ numbers.length
      · simp [h_case]
        simp at h_case
        omega
      · simp [h_case]
        by_cases h_first : numbers[0]! % 2 = 0
        · have h_odd : numbers[0]! % 2 = 1 := h 0 (by simp; omega)
          rw [h_first] at h_odd
          simp at h_odd
        · simp [h_first]
          apply ih
          simp
          intros i hi
          exact h (i + 1) (by omega)

-- LLM HELPER
lemma implementation_correct_nonempty (numbers: List Nat) :
  implementation numbers ≠ [] → 
  ∃ i, i < numbers.length ∧
    numbers[i]! % 2 = 0 ∧
    (implementation numbers)[0]! = numbers[i]! ∧
    (implementation numbers)[1]! = i ∧
    (∀ j, j < numbers.length → j < i → (numbers[j]! % 2 = 1 ∨ numbers[i]! < numbers[j]!)) ∧
    (∀ k, k < numbers.length → numbers[k]! % 2 = 0 → numbers[i]! ≤ numbers[k]!) := by
  intro h
  unfold implementation at h ⊢
  have h_len : (find_min_even_aux numbers 0 0 0 false).length = 2 := by
    have h_len_cases := find_min_even_aux_spec numbers 0 0 0 false
    cases h_len_cases with
    | inl h_empty => 
      rw [h_empty] at h
      simp at h
    | inr h_two => exact h_two
  have h_exists : ∃ i, i < numbers.length ∧ numbers[i]! % 2 = 0 := by
    by_contra h_contra
    push_neg at h_contra
    have h_empty : find_min_even_aux numbers 0 0 0 false = [] := by
      rw [← implementation_correct_empty]
      unfold implementation
      rfl
      exact h_contra
    rw [h_empty] at h
    simp at h
  obtain ⟨i, hi, h_even⟩ := h_exists
  use i
  constructor
  · exact hi
  constructor
  · exact h_even
  constructor
  · have h_get : (find_min_even_aux numbers 0 0 0 false)[0]! = numbers[i]! := by
      induction' numbers.length using Nat.strong_induction_on with k ih
      cases k with
      | zero => simp at hi
      | succ k' =>
        unfold find_min_even_aux
        simp
        by_cases h_case : 0 ≥ numbers.length
        · simp [h_case]
          simp at hi
          simp at h_case
          omega
        · simp [h_case]
          by_cases h_first : numbers[0]! % 2 = 0
          · simp [h_first]
            simp [Bool.not_false_eq_true]
            have h_min : numbers[0]! ≤ numbers[i]! := by
              apply Nat.le_refl
            by_cases h_eq : i = 0
            · simp [h_eq]
              induction' k' using Nat.strong_induction_on with m ihm
              cases m with
              | zero =>
                unfold find_min_even_aux
                simp
                by_cases h_len : 1 ≥ numbers.length
                · simp [h_len]
                · simp [h_len]
                  by_cases h_next : numbers[1]! % 2 = 0
                  · simp [h_next]
                    by_cases h_comp : numbers[1]! < numbers[0]!
                    · simp [h_comp]
                      apply ihm
                      simp
                    · simp [h_comp]
                      apply ihm
                      simp
                  · simp [h_next]
                    apply ihm
                    simp
              | succ m' =>
                apply ihm
                simp
            · apply ih
              simp
          · simp [h_first]
            apply ih
            simp
    exact h_get
  constructor
  · have h_get : (find_min_even_aux numbers 0 0 0 false)[1]! = i := by
      induction' numbers.length using Nat.strong_induction_on with k ih
      cases k with
      | zero => simp at hi
      | succ k' =>
        unfold find_min_even_aux
        simp
        by_cases h_case : 0 ≥ numbers.length
        · simp [h_case]
          simp at hi
          simp at h_case
          omega
        · simp [h_case]
          by_cases h_first : numbers[0]! % 2 = 0
          · simp [h_first]
            simp [Bool.not_false_eq_true]
            by_cases h_eq : i = 0
            · simp [h_eq]
              induction' k' using Nat.strong_induction_on with m ihm
              cases m with
              | zero =>
                unfold find_min_even_aux
                simp
                by_cases h_len : 1 ≥ numbers.length
                · simp [h_len]
                · simp [h_len]
                  by_cases h_next : numbers[1]! % 2 = 0
                  · simp [h_next]
                    by_cases h_comp : numbers[1]! < numbers[0]!
                    · simp [h_comp]
                      apply ihm
                      simp
                    · simp [h_comp]
                      apply ihm
                      simp
                  · simp [h_next]
                    apply ihm
                    simp
              | succ m' =>
                apply ihm
                simp
            · apply ih
              simp
          · simp [h_first]
            apply ih
            simp
    exact h_get
  constructor
  · intro j hj hj_lt
    left
    by_contra h_contra
    have h_j_even : numbers[j]! % 2 = 0 := by
      cases Nat.mod_two_eq_zero_or_one (numbers[j]!) with
      | inl h_zero => exact h_zero
      | inr h_one => contradiction
    have h_min : numbers[i]! ≤ numbers[j]! := by
      apply Nat.le_refl
    have h_lt : numbers[i]! < numbers[j]! := by
      apply Nat.lt_of_le_of_ne
      exact h_min
      intro h_eq
      have h_idx : i ≤ j := by
        apply Nat.le_refl
      have h_idx_lt : i < j := by
        apply Nat.lt_of_le_of_ne
        exact h_idx
        intro h_eq_idx
        rw [h_eq_idx] at hj_lt
        exact Nat.lt_irrefl j hj_lt
      exact Nat.lt_irrefl i (Nat.lt_trans hj_lt h_idx_lt)
    exact Nat.lt_irrefl numbers[i]! (Nat.lt_trans h_lt (Nat.le_refl numbers[j]!))
  · intro k hk hk_even
    apply Nat.le_refl

theorem correctness
(numbers: List Nat)
: problem_spec implementation numbers
:= by
  unfold problem_spec
  let spec := fun result => 
    (result.length = 0 ↔ ∀ i, i < numbers.length → numbers[i]! % 2 = 1) ∧
    (result.length = 2 ↔ ∃ i, i < numbers.length ∧
      numbers[i]! % 2 = 0 ∧
      result[0]! = numbers[i]! ∧
      result[1]! = i ∧
      (∀ j, j < numbers.length → j < i → (numbers[j]! % 2 = 1 ∨ numbers[i]! < numbers[j]!)) ∧
      (∀ k, k < numbers.length → numbers[k]! % 2 = 0 → numbers[i]! ≤ numbers[k]!))
  
  use implementation numbers
  constructor
  · rfl
  · constructor
    · constructor
      · intro h
        rw [← implementation_correct_empty]
        exact h
      · intro h
        rw [implementation_correct_empty]
        exact h
    · constructor
      · intro h
        have h_len := implementation_length numbers
        cases h_len with
        | inl h_empty => 
          rw [h_empty] at h
          simp at h
        | inr h_two =>
          rw [h_two] at h
          simp at h
          have h_nonempty : implementation numbers ≠ [] := by
            intro h_contra
            rw [h_contra] at h_two
            simp at h_two
          exact implementation_correct_nonempty numbers h_nonempty
      · intro h
        have h_len := implementation_length numbers
        cases h_len with
        | inl h_empty =>
          rw [h_empty]
          simp
          rw [implementation_correct_empty] at h_empty
          obtain ⟨i, hi, h_even, _, _, _, _⟩ := h
          have h_odd : numbers[i]! % 2 = 1 := h_empty i hi
          rw [h_even] at h_odd
          simp at h_odd
        | inr h_two =>
          exact h_two