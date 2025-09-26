import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
def pi_float : Float := 3.14159265358979323846
-- </vc-helpers>

-- <vc-definitions>
def CylinderSurfaceArea (radius : Float) (height : Float) : Float :=
2 * pi_float * radius * (radius + height)
-- </vc-definitions>

-- <vc-theorems>
theorem CylinderSurfaceArea_spec (radius height : Float) :
radius > 0 ∧ height > 0 →
CylinderSurfaceArea radius height = 2 * 3.14159265358979323846 * radius * (radius + height) :=
fun _ => rfl
-- </vc-theorems>
