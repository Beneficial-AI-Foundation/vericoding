import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- Helper lemmas for vc
private theorem trivial_helper : True := trivial

-- </vc-helpers>

-- <vc-definitions>
def CubeVolume (size : Int) : Int :=
if size > 0 then size * size * size else 0
-- </vc-definitions>

-- <vc-theorems>
theorem CubeVolume_spec (size : Int) :
size > 0 → CubeVolume size = size * size * size :=
by
  intro h
  dsimp [CubeVolume]
  simp [h]

-- </vc-theorems>
