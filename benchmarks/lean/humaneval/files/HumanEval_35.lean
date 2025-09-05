/- 
function_signature: "def max_element(l: list)"
docstring: |
    Return maximum element in the list.
test_cases:
  - input: [1, 2, 3]
    output: 3
  - input: [5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10]
    output: 123
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (l: List Int) : Int :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: List Int → Int)
-- inputs
(l: List Int) :=
-- spec
let spec (result: Int) :=
  l.length > 0 →
  ((∀ i, i < l.length → l[i]! ≤ result) ∧
  (∃ i, i < l.length ∧ l[i]! = result));
-- program termination
∃ result, implementation l = result ∧
spec result

theorem correctness
(l: List Int)
: problem_spec implementation l
:=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation [1, 2, 3] = 3
-- #test implementation [5, 3, -5, 2, -3, 3, 9, 0, 123, 1, -10] = 123