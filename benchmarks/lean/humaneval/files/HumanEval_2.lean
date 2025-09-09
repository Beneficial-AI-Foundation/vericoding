import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

def problem_spec
-- function signature
(impl: Rat → Rat)
-- inputs
(number: Rat) :=
-- spec
let spec (res) :=
0 ≤ res ∧
res < 1 ∧
number.floor + res = number;
number > 0 →
-- program terminates
(∃ result, impl number = result ∧
-- return value satisfies spec
spec result)

-- <vc-helpers>

-- </vc-helpers>

-- <vc-description>
/-
function_signature: "def truncate_number(number: float) -> float"
docstring: |
    Given a positive floating point number, it can be decomposed into
    and integer part (largest integer smaller than given number) and decimals
    (leftover part always smaller than 1).

    Return the decimal part of the number.
test_cases:
  - input: 3.5
    expected_output: 0.5
-/
-- </vc-description>

-- <vc-spec>
def implementation (number: Rat) : Rat :=
-- </vc-spec>
-- <vc-code>
sorry
-- </vc-code>

-- <vc-theorem>
theorem correctness
(number: Rat)
: problem_spec implementation number :=
-- </vc-theorem>
-- <vc-proof>
by sorry
-- </vc-proof>

-- #test implementation 3.5 = 0.5