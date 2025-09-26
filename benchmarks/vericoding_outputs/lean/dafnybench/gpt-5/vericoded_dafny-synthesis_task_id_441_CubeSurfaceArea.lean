import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
/-- Marker to note: no helpers required for this file. -/
def vcHelpersMarker : True := True.intro
-- </vc-helpers>

-- <vc-definitions>
def CubeSurfaceArea (size : Int) : Int :=
if size > 0 then 6 * size * size else 0
-- </vc-definitions>

-- <vc-theorems>
theorem CubeSurfaceArea_spec (size : Int) :
size > 0 → CubeSurfaceArea size = 6 * size * size :=
by
  intro h
  simp [CubeSurfaceArea, h]
-- </vc-theorems>
