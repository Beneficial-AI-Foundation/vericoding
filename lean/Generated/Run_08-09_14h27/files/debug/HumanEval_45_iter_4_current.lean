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
  (a * h) / 2

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
:= by
  use (a * h) / 2
  simp [implementation]
  intro ha_zero
  constructor
  · by_cases h_case : a = 0
    · left
      exact h_case
    · exfalso
      exact h_case ha_zero
  · intro ha_nonzero
    exfalso
    exact ha_nonzero ha_zero

-- #test implementation 5 3 = 7.5
-- #test implementation 8 2 = 8.0