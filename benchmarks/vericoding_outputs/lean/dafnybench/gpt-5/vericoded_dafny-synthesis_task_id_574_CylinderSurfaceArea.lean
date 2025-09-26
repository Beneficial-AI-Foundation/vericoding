import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
def twoPi : Float := 2 * 3.14159265358979323846

-- LLM HELPER
@[simp] theorem twoPi_mul (r h : Float) :
  twoPi * r * (r + h) = 2 * 3.14159265358979323846 * r * (r + h) := rfl
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
  intro h
  rfl
-- </vc-theorems>
