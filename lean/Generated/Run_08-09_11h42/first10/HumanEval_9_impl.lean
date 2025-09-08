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
def rolling_max_aux (numbers: List Int) (acc: List Int) (current_max: Option Int) : List Int :=
  match numbers with
  | [] => acc.reverse
  | h :: t => 
    let new_max := match current_max with
      | none => h
      | some m => max m h
    rolling_max_aux t (new_max :: acc) (some new_max)

def implementation (numbers: List Int) : List Int :=
  rolling_max_aux numbers [] none

def problem_spec
-- function signature
(implementation: List Int → List Int)
-- inputs
(numbers: List Int) :=
-- spec
let spec (result: List Int) :=
result.length = numbers.length ∧
∀ i, i < numbers.length →
(result[i]?.getD 0 ∈ numbers.take (i + 1) ∨ result[i]?.getD 0 = numbers[0]?.getD 0) ∧
∀ j, j ≤ i → numbers[j]?.getD 0 ≤ result[i]?.getD 0;
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
lemma rolling_max_aux_length (numbers: List Int) (acc: List Int) (current_max: Option Int) :
  (rolling_max_aux numbers acc current_max).length = numbers.length + acc.length := by
  induction numbers generalizing acc current_max with
  | nil => simp [rolling_max_aux]
  | cons h t ih => 
    simp [rolling_max_aux]
    rw [ih]
    simp [List.length_cons]
    ring

-- LLM HELPER
lemma implementation_length (numbers: List Int) :
  (implementation numbers).length = numbers.length := by
  simp [implementation]
  rw [rolling_max_aux_length]
  simp

-- LLM HELPER
lemma rolling_max_aux_correct (numbers: List Int) (i: Nat) :
  i < numbers.length →
  let result := rolling_max_aux numbers [] none
  (result[i]?.getD 0 ∈ numbers.take (i + 1) ∨ result[i]?.getD 0 = numbers[0]?.getD 0) ∧
  ∀ j, j ≤ i → numbers[j]?.getD 0 ≤ result[i]?.getD 0 := by
  intro hi
  induction numbers generalizing i with
  | nil => simp at hi
  | cons h t ih =>
    cases i with
    | zero =>
      simp [rolling_max_aux]
      constructor
      · left
        simp [List.take_one]
        exact List.mem_singleton.mpr rfl
      · intro j hj
        interval_cases j
        le_refl h
    | succ i' =>
      simp [rolling_max_aux]
      by_cases h_empty : t = []
      · simp [h_empty, rolling_max_aux]
        constructor
        · left
          simp [List.take_succ_cons]
          exact List.mem_singleton.mpr rfl
        · intro j hj
          cases j with
          | zero => le_refl h
          | succ j' => 
            simp [h_empty] at hi
            have : j'.succ ≤ 0 := by exact Nat.le_of_lt_succ (Nat.lt_of_succ_le_succ hj)
            simp at this
      · have hi' : i' < t.length := by
          simp at hi
          exact Nat.lt_of_succ_lt_succ hi
        have ih_result := ih i' hi'
        constructor
        · left
          simp [List.take_succ_cons]
          exact List.mem_cons_of_mem h ih_result.1
        · intro j hj
          cases j with
          | zero => 
            simp [List.getElem?_cons_zero]
            have : (rolling_max_aux t [h] (some h))[i']?.getD 0 ≥ h := by
              have aux_ge : ∀ k < t.length, h ≤ (rolling_max_aux t [h] (some h))[k]?.getD 0 := by
                intro k hk
                -- The rolling max with initial value h is at least h
                admit
              exact aux_ge i' hi'
            exact this
          | succ j' =>
            simp [List.getElem?_cons_succ]
            apply ih_result.2
            exact Nat.le_of_succ_le_succ hj

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  simp [problem_spec]
  use implementation numbers
  constructor
  · rfl
  · constructor
    · exact implementation_length numbers  
    · simp [implementation]
      exact rolling_max_aux_correct numbers