-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def CalculateLoss (costPrice : Int) (sellingPrice : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem CalculateLoss_spec (costPrice : Int) (sellingPrice : Int) :
costPrice ≥ 0 ∧ sellingPrice ≥ 0 →
((costPrice > sellingPrice → CalculateLoss costPrice sellingPrice = costPrice - sellingPrice) ∧
(costPrice ≤ sellingPrice → CalculateLoss costPrice sellingPrice = 0)) :=
sorry
-- </vc-theorems>