import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: No additional helpers needed for this implementation
-- </vc-helpers>

-- <vc-definitions>
def CubeSurfaceArea (size : Int) : Int :=
6 * size * size
-- </vc-definitions>

-- <vc-theorems>
theorem CubeSurfaceArea_spec (size : Int) :
size > 0 → CubeSurfaceArea size = 6 * size * size :=
fun h => rfl
-- </vc-theorems>
