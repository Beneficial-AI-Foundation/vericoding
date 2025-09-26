import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def CubeVolume (size : Int) : Int :=
size * size * size
-- </vc-definitions>

-- <vc-theorems>
theorem CubeVolume_spec (size : Int) :
size > 0 → CubeVolume size = size * size * size :=
by
  intro h_pos
  rfl
-- </vc-theorems>
