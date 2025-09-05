/- 
function_signature: "def greatest_common_divisor(a: int, b: int) -> int"
docstring: |
    Return a greatest common divisor of two integers a and b
test_cases:
  - input:
      - 25
      - 15
    expected_output: 5
  - input:
      - 3
      - 5
    expected_output: 1
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (a b: Int) : Int :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: Int → Int → Int)
-- inputs
(a b: Int) :=
-- spec
let spec (result: Int) :=
(result ∣ a) ∧
(result ∣ b) ∧
(∀ (d': Int),
(d' > 0) → (d' ∣ a) → (d' ∣ b) →
d' ≤ result);
-- program termination
∃ result, implementation a b = result ∧
spec result

theorem correctness
(a b: Int)
: problem_spec implementation a b
:=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation 25 15 = 5
-- #test implementation 3 5 = 1