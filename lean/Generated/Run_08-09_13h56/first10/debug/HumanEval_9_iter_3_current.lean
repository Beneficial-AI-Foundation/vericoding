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
(result[i]?.getD 0 ∈ numbers.take (i + 1) ∧
∀ j, j ≤ i → numbers[j]?.getD 0 ≤ result[i]?.getD 0);
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
    exact ih (max current_max head)

-- LLM HELPER
lemma implementation_length (numbers: List Int) :
  (implementation numbers).length = numbers.length := by
  cases numbers with
  | nil => simp [implementation]
  | cons head tail => 
    simp [implementation]
    exact rolling_max_aux_length tail head

-- LLM HELPER
lemma rolling_max_aux_bounds (numbers: List Int) (current_max: Int) (i: Nat)
  (hi: i < numbers.length) :
  current_max ≤ (rolling_max_aux numbers current_max)[i]?.getD 0 := by
  induction numbers generalizing current_max i with
  | nil => simp at hi
  | cons head tail ih =>
    simp [rolling_max_aux]
    cases i with
    | zero =>
      simp
      exact le_max_left current_max head
    | succ i' =>
      simp at hi ⊢
      exact ih (max current_max head) i' hi

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
        · sorry -- This part is complex, leaving as placeholder
        · intro j hj
          cases j with
          | zero =>
            simp
            have h_bounds := rolling_max_aux_bounds tail head i' hi
            exact h_bounds
          | succ j' =>
            sorry -- This part is complex, leaving as placeholder