import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- no helper code required for this file
-- </vc-helpers>

-- <vc-definitions>
def CubeVolume (size : Int) : Int :=
if h : size > 0 then size * size * size else 0
-- </vc-definitions>

-- <vc-theorems>
theorem CubeVolume_spec (size : Int) :
size > 0 → CubeVolume size = size * size * size :=
by
  intro h
  simp [CubeVolume, h]
-- </vc-theorems>
