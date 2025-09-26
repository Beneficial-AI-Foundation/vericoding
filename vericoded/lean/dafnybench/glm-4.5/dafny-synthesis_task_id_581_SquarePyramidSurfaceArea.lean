import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>

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
  intro h_base_pos h_height_pos
  unfold SquarePyramidSurfaceArea
  rfl
-- </vc-theorems>
