/- 
function_signature: "def incr_list(numbers: List[Int]) -> List[Int]"
docstring: |
    incr_list takes a list of integers as input and returns a new list
    where each element is incremented by 1.
test_cases:
  - input: []
    expected_output: []
  - input: [1, 3, -2, 1]
    expected_output: [2, 4, -1, 2]
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (numbers: List Int) : List Int :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: List Int → List Int)
-- inputs
(numbers: List Int) :=
-- spec
let spec (result: List Int) :=
  (result.length = numbers.length) ∧
  ∀ i, i < numbers.length →
  result[i]! = numbers[i]! + 1
-- -- program termination
∃ result, implementation numbers = result ∧
spec result

theorem correctness
(numbers : List Int)
: problem_spec implementation numbers
:=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation [1, 2, 3] = [2, 3, 4]
-- #test implementation [5, 3, 5, 2, 3, 3, 9, 0, 123] = [6, 4, 6, 3, 4, 4, 10, 1, 124]