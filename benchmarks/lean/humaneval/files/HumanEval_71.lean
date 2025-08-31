/- 
function_signature: "def triangle_area(a: float, b: float, c: float) -> float"
docstring: |
    Given the lengths of the three sides of a triangle. Return the area of the triangle rounded to 2 decimal points
    if the three sides form a valid triangle. Otherwise return -1. Three sides make a valid triangle when the sum of
    any two sides is greater than the third side.
test_cases:
  - input: (3, 4, 5)
    expected_output: 6
  - input: (1, 2, 10)
    expected_output: -1
-/

import Imports.AllImports

-- <vc-helpers>
-- </vc-helpers>

def implementation (a: Rat) (b: Rat) (c: Rat): Rat :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: Rat → Rat → Rat → Rat)
-- inputs
(a: Rat) (b: Rat) (c: Rat) :=
-- spec
let spec (result : Rat) :=
  let is_valid_triangle :=
    (a + b > c) ∧  (a + c > b) ∧ (b + c > a);
  let s :=
    (a + b + c) / 2;
  if is_valid_triangle then
    |result^2 - (s * (s-a) * (s-b) * (s-c))| ≤ ((1: Rat)/10000)
  else
    result = -1
-- program termination
∃ result, implementation a b c = result ∧
spec result

theorem correctness
(a: Rat) (b: Rat) (c: Rat)
: problem_spec implementation a b c
:=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation 3 4 5 = 6.00
-- #test implementation 1 2 10 = -1
-- #test implementation 4 8 5 = 8.18
-- #test implementation 2 2 2 = 1.73
-- #test implementation 1 2 3 = -1
-- #test implementation 10 5 7 = 16.25
-- #test implementation 2 6 3 = -1
-- #test implementation 1 1 1 =  0.43
-- #test implementation 2 2 10 = -1