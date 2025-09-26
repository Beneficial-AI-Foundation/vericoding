import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- No additional helpers needed
-- </vc-helpers>

-- <vc-definitions>
def CountArrays (arrays : Array (Array Int)) : Int :=
arrays.size
-- </vc-definitions>

-- <vc-theorems>
theorem CountArrays_spec (arrays : Array (Array Int)) :
let count := CountArrays arrays
count ≥ 0 ∧ count = arrays.size :=
by
  simp [CountArrays, Nat.cast_nonneg]
-- </vc-theorems>
