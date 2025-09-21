-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def CylinderLateralSurfaceArea (radius : Float) (height : Float) : Float :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem CylinderLateralSurfaceArea_spec (radius height : Float) :
radius > 0 ∧ height > 0 →
CylinderLateralSurfaceArea radius height = 2 * (radius * height) * 3.14 :=
sorry
-- </vc-theorems>