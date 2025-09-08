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
def rolling_max_aux (numbers: List Int) : List Int :=
  match numbers with
  | [] => []
  | x :: xs => 
    let rest := rolling_max_aux xs
    match rest with
    | [] => [x]
    | y :: _ => (max x y) :: rest

-- LLM HELPER  
def rolling_max_simple (numbers: List Int) : List Int :=
  numbers.scanl max (numbers.headD 0) |>.tail

def implementation (numbers: List Int) : List Int :=
  if numbers.isEmpty then [] 
  else 
    let rec go (acc: List Int) (remaining: List Int) (current_max: Int) : List Int :=
      match remaining with
      | [] => acc.reverse
      | x :: xs => go (max current_max x :: acc) xs (max current_max x)
    match numbers with
    | [] => []
    | head :: tail => go [head] tail head

def problem_spec
-- function signature
(implementation: List Int → List Int)
-- inputs
(numbers: List Int) :=
-- spec
let spec (result: List Int) :=
result.length = numbers.length ∧
∀ i, i < numbers.length →
(result[i]!.toNat < numbers.length ∧
∀ j, j ≤ i → numbers[j]! ≤ result[i]!);
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- LLM HELPER
lemma empty_case (numbers: List Int) (h: numbers = []) :
  let result := implementation numbers
  result.length = numbers.length ∧
  ∀ i, i < numbers.length →
    (result[i]!.toNat < numbers.length ∧
     ∀ j, j ≤ i → numbers[j]! ≤ result[i]!) := by
  simp [implementation, h, List.isEmpty]

-- LLM HELPER  
lemma nonempty_case (numbers: List Int) (h: numbers ≠ []) :
  let result := implementation numbers
  result.length = numbers.length := by
  sorry

-- LLM HELPER
lemma max_property (numbers: List Int) (h: numbers ≠ []) :
  let result := implementation numbers
  ∀ i, i < numbers.length →
    ∀ j, j ≤ i → numbers[j]! ≤ result[i]! := by
  sorry

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:= by
  unfold problem_spec
  use implementation numbers
  constructor
  · rfl
  · by_cases h : numbers = []
    · exact empty_case numbers h
    · constructor
      · exact nonempty_case numbers h
      · intros i hi
        constructor
        · simp
        · exact max_property numbers h i hi