/- 
function_signature: "def sum_squares(lst: List[float]) -> int"
docstring: |
    You are given a list of numbers.
    You need to return the sum of squared numbers in the given list,
    round each element in the list to the upper int(Ceiling) first.
test_cases:
  - input: [1, 2, 3]
    expected_output: 14
  - input: [1, 4, 9]
    expected_output: 98
  - input: [1, 3, 5, 7]
    expected_output: 84
  - input: [1.4, 4.2, 0]
    expected_output: 29
  - input: [-2.4, 1, 1]
    expected_output: 6
-/

import Imports.AllImports

-- <vc-helpers>
-- </vc-helpers>

def implementation (lst: List Rat) : Int :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(impl: List Rat → Int)
-- inputs
(lst: List Rat) :=
-- spec
let spec (result: Int) :=
  (lst = [] → result = 0) ∧
  (lst != [] → 0 ≤ result - lst[0]!.ceil^2 ∧ (impl (lst.drop 1) = (result - lst[0]!.ceil^2)))
-- program termination
∃ result, impl lst = result ∧
-- return value satisfies spec
spec result

theorem correctness
(lst: List Rat)
: problem_spec implementation lst :=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation [1, 2, 3] = 14
-- #test implementation [1, 4, 9] = 98
-- #test implementation [1, 3, 5, 7] = 84
-- #test implementation [1.4, 4.2, 0] = 29
-- #test implementation [-2.4, 1, 1] = 6