import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

def problem_spec
-- function signature
(implementation: List Rat → List Rat)
-- inputs
(numbers: List Rat) :=
-- spec
let spec (result: List Rat) :=
2 ≤ numbers.length →
let min_elem := numbers.min?.get!;
let max_elem := numbers.max?.get!;
let range := max_elem - min_elem;
result.length = numbers.length ∧
∀ i, i < numbers.length →
(min_elem ≠ max_elem →
result[i]! = (numbers[i]! - min_elem) / range) ∧
(min_elem = max_elem →
result[i]! = 0);
-- program termination
∃ result, implementation numbers = result ∧
spec result

-- <vc-helpers>

-- </vc-helpers>

-- <vc-description>
/-
function_signature: "def rescale_to_unit(numbers: List[float]) -> List[float]"
docstring: |
    Given list of numbers (of at least two elements), apply a linear transform to that list,
    such that the smallest number will become 0 and the largest will become 1
test_cases:
  - input: [1.0, 2.0, 3.0, 4.0, 5.0]
    expected_output: [0.0, 0.25, 0.5, 0.75, 1.0]
-/
-- </vc-description>

-- <vc-spec>
def implementation (numbers: List Rat): List Rat :=
-- </vc-spec>
-- <vc-code>
sorry
-- </vc-code>

-- <vc-theorem>
theorem correctness
(numbers: List Rat)
: problem_spec implementation numbers
:=
-- </vc-theorem>
-- <vc-proof>
by
  sorry
-- </vc-proof>

-- #test implementation [1.0, 2.0, 3.0, 4.0, 5.0] = [0.0, 0.25, 0.5, 0.75, 1.0]