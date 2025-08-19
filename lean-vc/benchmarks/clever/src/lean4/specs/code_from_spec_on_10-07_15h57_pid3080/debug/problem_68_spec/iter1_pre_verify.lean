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
  sorry

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
    sorry
  · intro h
    unfold implementation
    sorry

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
  sorry

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
        rw [implementation_correct_empty] at h
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
        | inr h_two =>
          exact h_two