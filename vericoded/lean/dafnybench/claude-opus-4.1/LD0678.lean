import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def PentagonPerimeter (side : Int) : Int :=
5 * side
-- </vc-definitions>

-- <vc-theorems>
theorem PentagonPerimeter_spec (side : Int) :
side > 0 → PentagonPerimeter side = 5 * side :=
by
  intro h
  rfl
-- </vc-theorems>
