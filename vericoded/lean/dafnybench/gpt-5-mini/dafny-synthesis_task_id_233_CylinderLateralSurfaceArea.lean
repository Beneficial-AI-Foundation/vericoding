import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
def piApprox : Float := 3.14

-- </vc-helpers>

-- <vc-definitions>
def CylinderLateralSurfaceArea (radius : Float) (height : Float) : Float :=
2 * (radius * height) * piApprox
-- </vc-definitions>

-- <vc-theorems>
theorem CylinderLateralSurfaceArea_spec (radius height : Float) :
radius > 0 ∧ height > 0 →
CylinderLateralSurfaceArea radius height = 2 * (radius * height) * 3.14 :=
by intro _; rfl
-- </vc-theorems>
