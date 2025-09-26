import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def CylinderLateralSurfaceArea (radius : Float) (height : Float) : Float :=
2 * (radius * height) * 3.14
-- </vc-definitions>

-- <vc-theorems>
theorem CylinderLateralSurfaceArea_spec (radius height : Float) :
radius > 0 ∧ height > 0 →
CylinderLateralSurfaceArea radius height = 2 * (radius * height) * 3.14 :=
fun _ => rfl
-- </vc-theorems>
