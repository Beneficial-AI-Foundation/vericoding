import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- No helpers needed for this verification task.
-- </vc-helpers>

-- <vc-definitions>
def PentagonPerimeter (side : Int) : Int :=
5 * side
-- </vc-definitions>

-- <vc-theorems>
theorem PentagonPerimeter_spec (side : Int) :
side > 0 → PentagonPerimeter side = 5 * side :=
by
  intro _
  simp [PentagonPerimeter]
-- </vc-theorems>
