/- 
function_signature: "def solve(n: list[int]) -> int"
docstring: |
    Given a non-empty list of integers lst, add the even elements that are at odd indices.
test_cases:
  - input: [4, 2, 6, 7]
    output: 2
-/

import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap

-- <vc-helpers>
-- </vc-helpers>

def implementation (lst: List Int) : Int :=
-- <vc-implementation>
  sorry
-- </vc-implementation>

def problem_spec
-- function signature
(implementation: List Int → Int)
-- inputs
(lst: List Int) :=
-- spec
let spec (result : Int) :=
  lst.length = 0 → result = 0 ∧
  lst.length > 0 →
    if lst.length > 1 then
      result = (if Even lst[1]! then lst[1]! else 0) + implementation (lst.drop 2)
    else
      result = (if Even lst[1]! then lst[1]! else 0)
-- program termination
∃ result,
  implementation lst = result ∧
  spec result

theorem correctness
(lst: List Int)
: problem_spec implementation lst
:=
-- <vc-proof>
  sorry
-- </vc-proof>

-- #test implementation [4, 2, 6, 7] = 2