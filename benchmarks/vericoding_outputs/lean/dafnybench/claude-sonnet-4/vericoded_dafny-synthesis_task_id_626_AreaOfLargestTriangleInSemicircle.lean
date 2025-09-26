import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- Helper functions and lemmas for semicircle triangle area calculation
-- LLM HELPER: No additional helpers needed for this straightforward geometric calculation
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
  intro h_pos
  -- The largest triangle inscribed in a semicircle is a right triangle
  -- with base as diameter (2*radius) and height as radius
  -- Area = (1/2) * base * height = (1/2) * (2*radius) * radius = radius^2
  rfl
-- </vc-theorems>
