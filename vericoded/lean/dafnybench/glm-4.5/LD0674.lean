import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
theorem Array.size_nonneg {α} (arr : Array α) : (arr.size : Int) ≥ 0 := by
  apply Int.natCast_nonneg
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
  rw [CountArrays]
  constructor
  · exact Array.size_nonneg arrays
  · rfl
-- </vc-theorems>
