import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- No helpers needed for this simple definition
-- </vc-helpers>

-- <vc-definitions>
def CalculateLoss (costPrice : Int) (sellingPrice : Int) : Int :=
if costPrice > sellingPrice then costPrice - sellingPrice else 0
-- </vc-definitions>

-- <vc-theorems>
theorem CalculateLoss_spec (costPrice : Int) (sellingPrice : Int) :
costPrice ≥ 0 ∧ sellingPrice ≥ 0 →
((costPrice > sellingPrice → CalculateLoss costPrice sellingPrice = costPrice - sellingPrice) ∧
(costPrice ≤ sellingPrice → CalculateLoss costPrice sellingPrice = 0)) :=
by
  intro h
  constructor
  · intro hgt
    simp [CalculateLoss, if_pos hgt]
  · intro hle
    simp only [CalculateLoss]
    by_cases h : costPrice > sellingPrice
    · simp [if_pos h]
      exfalso
      linarith
    · simp [if_neg h]
-- </vc-theorems>
