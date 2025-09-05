/- 
function_signature: "def get_positive(l: list)"
docstring: |
    Return only positive numbers in the list.
test_cases:
  - input: [-1, 2, -4, 5, 6]
    expected_output: [2, 5, 6]
  - input: [5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10]
    expected_output: [5, 3, 2, 3, 9, 123, 1]
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (numbers: List Int): List Int :=
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
  result.all (λ x => x > 0 ∧ x ∈ numbers) ∧
  numbers.all (λ x => x > 0 → x ∈ result) ∧
  result.all (λ x => result.count x = numbers.count x);
-- program termination
∃ result,
  implementation numbers = result ∧
  spec result

theorem correctness
(numbers: List Int)
: problem_spec implementation numbers
:=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation [(-1), 2, (-4), 5, 6] = [2, 5, 6]
-- #test implementation [5, 3, (-5), 2, (-3), 3, 9, 0, 123, 1, (-10)] = [5, 3, 2, 3, 9, 123, 1]