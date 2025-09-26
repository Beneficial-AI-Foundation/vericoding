import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
def PentagonPerimeter_aux (side : Int) : Int := side * 5
-- </vc-helpers>

-- <vc-definitions>
def PentagonPerimeter (side : Int) : Int :=
PentagonPerimeter_aux side
-- </vc-definitions>

-- <vc-theorems>
theorem PentagonPerimeter_spec (side : Int) :
side > 0 → PentagonPerimeter side = 5 * side :=
by
  intros h_side_pos
  simp [PentagonPerimeter, PentagonPerimeter_aux]
  rw [Int.mul_comm]
-- </vc-theorems>
