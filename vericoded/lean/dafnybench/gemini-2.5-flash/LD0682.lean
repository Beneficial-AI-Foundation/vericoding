import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
def CubeVolume_impl (size : Int) : Int := size * size * size
-- </vc-helpers>

-- <vc-definitions>
def CubeVolume (size : Int) : Int :=
  CubeVolume_impl size
-- </vc-definitions>

-- <vc-theorems>
theorem CubeVolume_spec (size : Int) :
size > 0 → CubeVolume size = size * size * size :=
by
  intro h_pos
  simp [CubeVolume, CubeVolume_impl]
-- </vc-theorems>
