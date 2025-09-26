import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- No helper definitions required for this simple specification
-- </vc-helpers>

-- <vc-definitions>
def SquarePyramidSurfaceArea (baseEdge : Int) (height : Int) : Int :=
baseEdge * baseEdge + 2 * baseEdge * height
-- </vc-definitions>

-- <vc-theorems>
theorem SquarePyramidSurfaceArea_spec (baseEdge height : Int) :
baseEdge > 0 →
height > 0 →
SquarePyramidSurfaceArea baseEdge height = baseEdge * baseEdge + 2 * baseEdge * height :=
by
  intros hbe hht
  rfl
-- </vc-theorems>
