import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- no helpers needed
-- </vc-helpers>

-- <vc-definitions>
def MultipleReturns (x y : Int) : Int × Int :=
(x + y, x - y)
-- </vc-definitions>

-- <vc-theorems>
theorem MultipleReturns_spec (x y : Int) :
let (more, less) := MultipleReturns x y
more = x + y ∧ less = x - y :=
by
  simpa [MultipleReturns]
-- </vc-theorems>
