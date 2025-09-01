/- 
function_signature: "def monotonic(numbers: List[int]) -> Bool"
docstring: |
    Return True if list elements are monotonically increasing or decreasing.
test_cases:
  - input: [1, 2, 4, 20]
    expected_output: True
  - input: [1, 20, 4, 10]
    expected_output: False
  - input: [4, 1, 0, -10]
    expected_output: True
-/

import Imports.AllImports

-- <vc-helpers>
-- </vc-helpers>

def implementation (numbers: List Int) : Bool :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: List Int → Bool)
-- inputs
(numbers: List Int) :=
let non_ordered := ∃ i j,
i < numbers.length - 1 ∧
j < numbers.length - 1 ∧
(numbers[i]! < numbers[i+1]!) ∧
(numbers[j+1]! < numbers[j]!);
-- spec
let spec (result: Bool) :=
  1 < numbers.length →
  result ↔ ¬non_ordered;
-- program termination
∃ result, implementation numbers = result ∧
spec result

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation [1, 2, 4, 20] = true
-- #test implementation [1, 20, 4, 10] = false
-- #test implementation [4, 1, 0, -10] = true