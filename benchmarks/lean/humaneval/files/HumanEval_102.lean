/- 
function_signature: "def choose_num(x: int, y: int) -> int"
docstring: |
    This function takes two positive numbers x and y and returns the
    biggest even integer number that is in the range [x, y] inclusive. If
    there's no such number, then the function should return -1.
test_cases:
  - input: (12, 15)
    expected_output: 14
  - input: (13, 12)
    expected_output: -1
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (x: Int) (y: Int) : Int :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: Int → Int → Int)
-- inputs
(x: Int) (y: Int) :=
-- spec
let spec (result: Int) :=
  (result = -1 ∨ (x ≤ result ∧ result ≤ y ∧ Even result)) ∧
  (result = -1 ∨ (forall i: Int, (x ≤ i ∧ i ≤ y ∧ Even i) → result ≥ i)) ∧
  (result = -1 ↔ (x > y ∨ (x == y ∧ Odd x ∧ Odd y)))
-- program termination
∃ result, implementation x y = result ∧
spec result

theorem correctness
(x: Int) (y: Int)
: problem_spec implementation x y
:=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation 12 15 = 14
-- #test implementation 13 12 = -1
-- #test implementation 33 12354 = 12354
-- #test implementation 5234 5233 = -1
-- #test implementation 6 29 = 28
-- #test implementation 27 10 = (-1)
-- #test implementation 7 7 = -1
-- #test implementation 546 546 = 546