import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
@[simp] lemma int_coe_nat_nonneg (n : Nat) : ((n : Int) ≥ 0) := by
  simpa using (Int.ofNat_nonneg n)

-- </vc-helpers>

-- <vc-definitions>
def CountArrays (arrays : Array (Array Int)) : Int :=
(arrays.size : Int)
-- </vc-definitions>

-- <vc-theorems>
theorem CountArrays_spec (arrays : Array (Array Int)) :
let count := CountArrays arrays
count ≥ 0 ∧ count = arrays.size :=
by
  have h : (CountArrays arrays) ≥ 0 ∧ (CountArrays arrays) = arrays.size := by
    constructor
    · simpa [CountArrays] using (Int.ofNat_nonneg (arrays.size))
    · simp [CountArrays]
  simpa [CountArrays] using h
-- </vc-theorems>
