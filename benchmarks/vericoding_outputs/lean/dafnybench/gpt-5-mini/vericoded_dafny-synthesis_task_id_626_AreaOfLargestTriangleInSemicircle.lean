import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
/- No helpers required for this problem. -/
-- </vc-helpers>

-- <vc-definitions>
def AreaOfLargestTriangleInSemicircle (radius : Int) : Int :=
radius * radius
-- </vc-definitions>

-- <vc-theorems>
theorem AreaOfLargestTriangleInSemicircle_spec (radius : Int) :
radius > 0 →
AreaOfLargestTriangleInSemicircle radius = radius * radius :=
by
  intro _
  rfl
-- </vc-theorems>
