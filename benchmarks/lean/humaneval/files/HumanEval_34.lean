/- 
function_signature: "def unique(l: list)"
docstring: |
    Return sorted unique elements in a list.
test_cases:
  - input: [5, 3, 5, 2, 3, 3, 9, 0, 123]
    output: [0, 2, 3, 5, 9, 123]
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (l: List Int) : List Int :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: List Int → List Int)
-- inputs
(l: List Int) :=
-- spec
let spec (result: List Int) :=
  (∀ x, x ∈ result ↔ x ∈ l ∧ result.count x = 1) ∧
  List.Sorted Int.le result
-- program termination
∃ result,
  implementation l = result ∧
  spec result

theorem correctness
(l: List Int)
: problem_spec implementation l
:=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation [5, 3, 5, 2, 3, 3, 9, 0, 123] = [0, 2, 3, 5, 9, 123]