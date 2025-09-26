import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def CountArrays (arrays : Array (Array Int)) : Int :=
Int.ofNat arrays.size
-- </vc-definitions>

-- <vc-theorems>
theorem CountArrays_spec (arrays : Array (Array Int)) :
let count := CountArrays arrays
count ≥ 0 ∧ count = arrays.size :=
by
  simp only [CountArrays]
  constructor
  · exact Int.ofNat_zero_le arrays.size
  · rfl
-- </vc-theorems>
