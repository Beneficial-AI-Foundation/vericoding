import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- No additional helpers needed for this simple implementation
-- </vc-helpers>

-- <vc-definitions>
def AreaOfLargestTriangleInSemicircle (radius : Int) : Int :=
radius * radius
-- </vc-definitions>

-- <vc-theorems>
theorem AreaOfLargestTriangleInSemicircle_spec (radius : Int) :
radius > 0 →
AreaOfLargestTriangleInSemicircle radius = radius * radius :=
fun h => rfl
-- </vc-theorems>
