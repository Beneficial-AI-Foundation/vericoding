import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
def CountArrays_nat (arrays : Array (Array Int)) : Nat := arrays.size
-- </vc-helpers>

-- <vc-definitions>
def CountArrays (arrays : Array (Array Int)) : Int :=
Nat.cast arrays.size
-- </vc-definitions>

-- <vc-theorems>
theorem CountArrays_spec (arrays : Array (Array Int)) :
let count := CountArrays arrays
count ≥ 0 ∧ count = arrays.size :=
let count := CountArrays arrays;
  ⟨Int.natCast_nonneg arrays.size, rfl⟩
-- </vc-theorems>
