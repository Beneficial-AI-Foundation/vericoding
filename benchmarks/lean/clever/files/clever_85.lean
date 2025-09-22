-- <vc-preamble>
import Mathlib
import Mathlib.Algebra.Polynomial.Basic
import Std.Data.HashMap
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def implementation (lst: List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
:= by
  sorry
-- </vc-theorems>