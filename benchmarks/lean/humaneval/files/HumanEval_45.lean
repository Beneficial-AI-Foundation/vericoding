/- 
function_signature: "def triangle_area(a: float, h: float) -> float"
docstring: |
    Given length of a side and high return area for a triangle.
test_cases:
  - input: (5, 3)
    expected_output: 7.5
  - input: (8, 2)
    expected_output: 8.0
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (a h: Rat) : Rat :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: Rat → Rat -> Rat)
-- inputs
(a h: Rat) :=
-- spec
let spec (result: Rat) :=
  a = 0 → result = 0 ∧
  (a ≠ 0 → (2 * result) / a = h);
-- -- program termination
∃ result, implementation a h = result ∧
spec result

theorem correctness
(a h : Rat)
: problem_spec implementation a h
:=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation 5 3 = 7.5
-- #test implementation 8 2 = 8.0