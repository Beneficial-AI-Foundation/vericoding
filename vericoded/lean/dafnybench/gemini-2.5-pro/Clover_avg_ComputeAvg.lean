import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- This section is intentionally left blank as no helper theorems are needed for the corrected implementation.
-- </vc-helpers>

-- <vc-definitions>
def ComputeAvg (a b : Int) : Int :=
(a + b) / 2
-- </vc-definitions>

-- <vc-theorems>
theorem ComputeAvg_spec (a b : Int) :
ComputeAvg a b = (a + b) / 2 :=
by simp [ComputeAvg]
-- </vc-theorems>
