import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
theorem int_not_gt_of_le {a b : Int} (h : a ≤ b) : ¬ a > b := by
  exact not_lt_of_ge (show b ≥ a from h)
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
  intro _hnonneg
  constructor
  · intro hgt
    simp [CalculateLoss, hgt]
  · intro hle
    have hnot : ¬ costPrice > sellingPrice := int_not_gt_of_le hle
    simp [CalculateLoss, hnot]
-- </vc-theorems>
