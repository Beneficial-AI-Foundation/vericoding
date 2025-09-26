import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
/-- Approximation of π used in the specification. -/
def piApprox : Float := 3.14

-- LLM HELPER
@[simp] theorem piApprox_eq : piApprox = (3.14 : Float) := rfl
-- </vc-helpers>

-- <vc-definitions>
def CylinderLateralSurfaceArea (radius : Float) (height : Float) : Float :=
2 * (radius * height) * 3.14
-- </vc-definitions>

-- <vc-theorems>
theorem CylinderLateralSurfaceArea_spec (radius height : Float) :
radius > 0 ∧ height > 0 →
CylinderLateralSurfaceArea radius height = 2 * (radius * height) * 3.14 :=
by
  intro _
  rfl
-- </vc-theorems>
