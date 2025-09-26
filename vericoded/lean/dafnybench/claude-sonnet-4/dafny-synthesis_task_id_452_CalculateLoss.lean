import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: lemmas for integer comparisons
lemma not_gt_of_le {a b : ℤ} (h : a ≤ b) : ¬(a > b) := not_lt_of_le h
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
  · intro h1
    unfold CalculateLoss
    simp [h1]
  · intro h2
    unfold CalculateLoss
    simp [not_gt_of_le h2]
-- </vc-theorems>
