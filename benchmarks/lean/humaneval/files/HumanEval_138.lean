import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

def problem_spec
-- function signature
(impl: Int → Bool)
-- inputs
(n: Int) :=
-- spec
let spec (result: Bool) :=
  let sum_exists := ∃ a b c d : Nat,
    Even a ∧
    Even b ∧
    Even c ∧
    Even d ∧
    (a + b + c + d = n);
  result = true ↔ sum_exists
-- program termination
∃ result, impl n = result ∧
-- return value satisfies spec
spec result

-- <vc-helpers>

-- </vc-helpers>

-- <vc-description>
/-
function_signature: "def is_equal_to_sum_even(n: int) -> Bool"
docstring: |
    Evaluate whether the given number n can be written as the sum of exactly 4 positive even numbers
test_cases:
  - input: 4
    expected_output: False
  - input: 6
    expected_output: False
  - input: 8
    expected_output: True
-/
-- </vc-description>

-- <vc-spec>
def implementation (n: Int) : Bool :=
-- </vc-spec>
-- <vc-code>
sorry
-- </vc-code>

-- <vc-theorem>
theorem correctness
(n: Int)
: problem_spec implementation n :=
-- </vc-theorem>
-- <vc-proof>
by
  sorry
-- </vc-proof>

-- #test implementation 4 = false
-- #test implementation 6 = false
-- #test implementation 8 = true