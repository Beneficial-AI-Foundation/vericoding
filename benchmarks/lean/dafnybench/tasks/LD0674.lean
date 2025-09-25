-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def CountArrays (arrays : Array (Array Int)) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem CountArrays_spec (arrays : Array (Array Int)) :
let count := CountArrays arrays
count ≥ 0 ∧ count = arrays.size :=
sorry
-- </vc-theorems>