-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def SquarePyramidSurfaceArea (baseEdge : Int) (height : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem SquarePyramidSurfaceArea_spec (baseEdge height : Int) :
baseEdge > 0 →
height > 0 →
SquarePyramidSurfaceArea baseEdge height = baseEdge * baseEdge + 2 * baseEdge * height :=
sorry
-- </vc-theorems>