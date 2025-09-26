import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- No helpers needed for this simple computation
-- </vc-helpers>

-- <vc-definitions>
def CylinderSurfaceArea (radius : Float) (height : Float) : Float :=
2 * 3.14159265358979323846 * radius * (radius + height)
-- </vc-definitions>

-- <vc-theorems>
theorem CylinderSurfaceArea_spec (radius height : Float) :
radius > 0 ∧ height > 0 →
CylinderSurfaceArea radius height = 2 * 3.14159265358979323846 * radius * (radius + height) :=
by
  intro ⟨hr, hh⟩
  unfold CylinderSurfaceArea
  rfl
-- </vc-theorems>
