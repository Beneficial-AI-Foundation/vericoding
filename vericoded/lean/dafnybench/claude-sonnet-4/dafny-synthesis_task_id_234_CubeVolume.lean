import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- No additional helpers needed for this implementation
-- </vc-helpers>

-- <vc-definitions>
def CubeVolume (size : Int) : Int :=
size * size * size
-- </vc-definitions>

-- <vc-theorems>
theorem CubeVolume_spec (size : Int) :
size > 0 → CubeVolume size = size * size * size :=
fun h => rfl
-- </vc-theorems>
