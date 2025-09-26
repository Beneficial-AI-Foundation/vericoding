import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
namespace VCHelpers
  -- Helper namespace reserved for future use; currently no additional lemmas required.
end VCHelpers
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
  intro _ _
  rfl
-- </vc-theorems>
