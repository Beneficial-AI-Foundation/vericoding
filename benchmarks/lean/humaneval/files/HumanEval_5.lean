/- 
function_signature: "def intersperse(numbers: List[int], delimeter: int) -> List[int]"
docstring: |
    Insert a number 'delimeter' between every two consecutive elements of input list `numbers'
test_cases:
  - input:
      - []
      - 4
    expected_output: []
  - input:
      - [1, 2, 3]
      - 4
    expected_output: [1, 4, 2, 4, 3]
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (numbers: List Int) (delimeter: Int) : List Int :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: List Int → Int → List Int)
-- inputs
(numbers: List Int)
(delimeter: Int) :=
-- spec
let spec (result: List Int) :=
(result.length = 0 ∧ result = numbers) ∨
(result.length = 2 ∧ numbers.length = 1 ∧
result[0]! = numbers[0]! ∧ result[1]! = delimeter) ∨
(result.length = 2 * numbers.length - 1 ∧
∀ i, i < numbers.length →
result[2 * i]! = numbers[i]! ∧
(0 < 2*i - 1 → result[2 * i - 1]! = delimeter));
-- program termination
∃ result, implementation numbers delimeter = result ∧
spec result

theorem correctness
(numbers: List Int)
(delimeter: Int)
: problem_spec implementation numbers delimeter
:=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation [1, 2, 3] 4 = [1, 4, 2, 4, 3]
-- #test implementation [] 4 = []
-- #test implementation [1] 4 = [1]