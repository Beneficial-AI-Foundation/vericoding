import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: no helpers needed
-- </vc-helpers>

-- <vc-definitions>
def ComputeAvg (a b : Int) : Int :=
(a + b) / 2
-- </vc-definitions>

-- <vc-theorems>
theorem ComputeAvg_spec (a b : Int) :
ComputeAvg a b = (a + b) / 2 :=
rfl
-- </vc-theorems>
