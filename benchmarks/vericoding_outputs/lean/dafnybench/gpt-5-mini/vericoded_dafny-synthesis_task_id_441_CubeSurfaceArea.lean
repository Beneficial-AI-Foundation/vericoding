import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
/- No additional helper lemmas are required for the simple surface-area definition below. This section kept intentionally minimal. -/

-- </vc-helpers>

-- <vc-definitions>
def CubeSurfaceArea (size : Int) : Int :=
6 * size * size

-- </vc-definitions>

-- <vc-theorems>
theorem CubeSurfaceArea_spec (size : Int) :
size > 0 → CubeSurfaceArea size = 6 * size * size :=
by
  intro _
  rfl

-- </vc-theorems>
