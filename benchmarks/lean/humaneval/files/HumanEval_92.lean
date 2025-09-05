/- 
function_signature: "def any_int(a: float, b: float, c: float) -> bool"
docstring: |
    Create a function that takes 3 numbers.
    Returns true if one of the numbers is equal to the sum of the other two, and all numbers are integers.
    Returns false in any other cases.
test_cases:
  - input: [5, 2, 7]
    expected_output: true
  - input: [3, 2, 2]
    expected_output: false
  - input: [3, -2, 1]
    expected_output: true
  - input: [3.6, -2.2, 2]
    expected_output: false
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (a: Rat) (b: Rat) (c: Rat) : Bool :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: Rat → Rat → Rat → Bool)
-- inputs
(a: Rat) (b: Rat) (c: Rat) :=
-- spec
let spec (result : Bool) :=
  let nums := [a, b, c];
  result = true ↔ ∃ i j k : ℕ, {i, j, k} ⊆ ({0, 1, 2} : Set ℕ) ∧ i ≠ j ∧ j ≠ k ∧ k ≠ i ∧ (nums[i]! + nums[j]! = nums[k]!) ∧ a.den = 1 ∧ a.den = b.den ∧ a.den = c.den
-- program termination
∃ result,
  implementation a b c = result ∧
  spec result

theorem correctness
(a: Rat) (b: Rat) (c: Rat)
: problem_spec implementation a b c
:=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation 5 2 7 = true
-- #test implementation 3 2 2 = false
-- #test implementation 3 (-2) 1 = true
-- #test implementation 3.6 (-2.2) 2 = false