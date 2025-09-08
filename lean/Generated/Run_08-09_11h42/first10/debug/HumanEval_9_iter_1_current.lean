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
(result[i]! ∈ numbers.take (i + 1) ∧
∀ j, j ≤ i → numbers[j]! ≤ result[i]!);
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
    simp

-- LLM HELPER
lemma implementation_length (numbers: List Int) :
  (implementation numbers).length = numbers.length := by
  simp [implementation]
  rw [rolling_max_aux_length]
  simp

-- LLM HELPER
lemma rolling_max_aux_spec (numbers: List Int) (acc: List Int) (current_max: Option Int) 
  (orig_numbers: List Int) (k: Nat) :
  orig_numbers = acc.reverse ++ numbers →
  k < orig_numbers.length →
  k < acc.length →
  (rolling_max_aux numbers acc current_max)[k]! = acc.reverse[k]! := by
  sorry

-- LLM HELPER
lemma max_in_list (a b : Int) (l : List Int) : a ∈ l → max a b ∈ b :: l := by
  intro h
  by_cases h' : a ≤ b
  · simp [max_def, h']
  · simp [max_def, h']
    exact h

-- LLM HELPER  
lemma max_ge_left (a b : Int) : a ≤ max a b := by
  simp [max_def]
  split <;> simp

-- LLM HELPER
lemma max_ge_right (a b : Int) : b ≤ max a b := by
  simp [max_def] 
  split <;> simp

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  simp [problem_spec]
  use implementation numbers
  constructor
  · rfl
  · simp [implementation]
    constructor
    · exact implementation_length numbers
    · sorry