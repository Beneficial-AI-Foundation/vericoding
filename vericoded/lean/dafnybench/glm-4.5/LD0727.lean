import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>

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
fun h_nonneg =>
  ⟨fun h_cost_gt_selling => by simp [CalculateLoss, h_cost_gt_selling],
   fun h_cost_le_selling => by simp [CalculateLoss, h_cost_le_selling]⟩
-- </vc-theorems>
