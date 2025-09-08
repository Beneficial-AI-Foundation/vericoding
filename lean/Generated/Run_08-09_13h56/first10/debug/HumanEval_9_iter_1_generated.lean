/- 
function_signature: "def rolling_max(numbers: List[int]) -> Tuple[int, int]"
docstring: |
  From a given list of integers, generate a list of rolling maximum element found until given moment
  in the sequence.
test_cases:
  - input: [1, 2, 3, 2, 3, 4, 2]
    expected_output: [1, 2, 3, 3, 3, 4, 4]
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

-- LLM HELPER
def rolling_max_aux (numbers: List Int) (current_max: Int) : List Int :=
  match numbers with
  | [] => []
  | head :: tail =>
    let new_max := max current_max head
    new_max :: rolling_max_aux tail new_max

def implementation (numbers: List Int) : List Int :=
  match numbers with
  | [] => []
  | head :: tail => head :: rolling_max_aux tail head

def problem_spec
-- function signature
(implementation: List Int → List Int)
-- inputs
(numbers: List Int) :=
-- spec
let spec (result: List Int) :=
result.length = numbers.length ∧
∀ i, i < numbers.length →
(result[i]! ∈ numbers.take (i + 1) ∧
∀ j, j ≤ i → numbers[j]! ≤ result[i]!);
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
lemma rolling_max_aux_length (numbers: List Int) (current_max: Int) :
  (rolling_max_aux numbers current_max).length = numbers.length := by
  induction numbers generalizing current_max with
  | nil => simp [rolling_max_aux]
  | cons head tail ih => 
    simp [rolling_max_aux]
    exact ih

-- LLM HELPER
lemma implementation_length (numbers: List Int) :
  (implementation numbers).length = numbers.length := by
  cases numbers with
  | nil => simp [implementation]
  | cons head tail => 
    simp [implementation]
    exact rolling_max_aux_length tail head

-- LLM HELPER
lemma max_in_list (a b : Int) : max a b = a ∨ max a b = b := by
  simp [max_def]
  by_cases h : a ≤ b
  · right; exact if_pos h
  · left; exact if_neg h

-- LLM HELPER
lemma rolling_max_aux_property (numbers: List Int) (current_max: Int) (i: Nat) 
  (hi: i < numbers.length) :
  let result := rolling_max_aux numbers current_max
  ∀ j, j ≤ i → numbers[j]! ≤ result[i]! := by
  induction numbers generalizing current_max i with
  | nil => simp at hi
  | cons head tail ih =>
    simp [rolling_max_aux]
    cases i with
    | zero =>
      intro j hj
      simp at hj
      simp [hj]
      exact le_max_right current_max head
    | succ i' =>
      simp at hi
      intro j hj
      cases j with
      | zero =>
        simp
        exact le_max_right current_max head
      | succ j' =>
        simp
        have h_max := le_max_left current_max head
        have h_ih := ih (max current_max head) i' hi (j' + 1) (by simp; exact Nat.succ_le_succ_iff.mp hj)
        simp at h_ih
        exact h_ih

-- LLM HELPER
lemma rolling_max_aux_elem_in_extended (numbers: List Int) (current_max: Int) (i: Nat)
  (hi: i < numbers.length) :
  let result := rolling_max_aux numbers current_max
  result[i]! ∈ (current_max :: numbers).take (i + 2) := by
  induction numbers generalizing current_max i with
  | nil => simp at hi
  | cons head tail ih =>
    simp [rolling_max_aux]
    cases i with
    | zero =>
      simp [List.take]
      cases max_in_list current_max head with
      | inl h => simp [h]; left; rfl
      | inr h => simp [h]; right; left; rfl
    | succ i' =>
      simp at hi
      simp [List.take]
      have h_ih := ih (max current_max head) i' hi
      simp at h_ih
      cases max_in_list current_max head with
      | inl h_max =>
        simp [h_max] at h_ih ⊢
        cases h_ih with
        | inl h1 => left; exact h1
        | inr h2 => right; exact List.mem_take_of_mem _ h2
      | inr h_max =>
        simp [h_max] at h_ih ⊢
        cases h_ih with
        | inl h1 => right; left; exact h1
        | inr h2 => right; exact List.mem_take_of_mem _ h2

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  simp [problem_spec]
  use implementation numbers
  constructor
  · rfl
  constructor
  · exact implementation_length numbers
  · intro i hi
    cases numbers with
    | nil => simp at hi
    | cons head tail =>
      simp [implementation] at hi ⊢
      cases i with
      | zero =>
        constructor
        · simp [List.take]; left; rfl
        · intro j hj
          simp at hj
          simp [hj]
      | succ i' =>
        simp at hi
        have h_aux_len := rolling_max_aux_length tail head
        simp [h_aux_len] at hi
        constructor
        · have h_mem := rolling_max_aux_elem_in_extended tail head i' hi
          simp at h_mem
          simp [List.take]
          cases h_mem with
          | inl h1 => left; exact h1
          | inr h2 => right; exact h2
        · intro j hj
          cases j with
          | zero =>
            simp
            have h_prop := rolling_max_aux_property tail head i' hi
            simp at h_prop
            have h_prop_0 := h_prop 0 (Nat.zero_le _)
            simp at h_prop_0
            exact le_max_right head (rolling_max_aux tail head)[i']!
          | succ j' =>
            simp
            have h_prop := rolling_max_aux_property tail head i' hi
            simp at h_prop
            exact h_prop (j' + 1) (Nat.succ_le_succ_iff.mp hj)

-- #test implementation [1, 2, 3, 2, 3, 4, 2] = [1, 2, 3, 3, 3, 4, 4]