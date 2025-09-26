import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
/- Helper utilities for verification conditions. -/
namespace VC_Helpers

/- No helpers required for this simple example. -/

end VC_Helpers
-- </vc-helpers>

-- <vc-definitions>
def ComputeAvg (a b : Int) : Int :=
(a + b) / 2
-- </vc-definitions>

-- <vc-theorems>
theorem ComputeAvg_spec (a b : Int) :
ComputeAvg a b = (a + b) / 2 :=
by rfl
-- </vc-theorems>
