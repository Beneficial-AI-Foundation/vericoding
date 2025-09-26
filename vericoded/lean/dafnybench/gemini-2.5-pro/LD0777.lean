import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>

-- LLM HELPER
theorem coe_decide_replacement {p : Prop} [Decidable p] : decide p = p := by
  by_cases h : p <;> simp [h]

-- </vc-helpers>

-- <vc-definitions>
def IsBreakEven (costPrice : Int) (sellingPrice : Int) : Bool :=
decide (costPrice = sellingPrice)
-- </vc-definitions>

-- <vc-theorems>
theorem IsBreakEven_spec (costPrice sellingPrice : Int) :
costPrice ≥ 0 ∧ sellingPrice ≥ 0 →
IsBreakEven costPrice sellingPrice = (costPrice = sellingPrice) :=
by simp [IsBreakEven, coe_decide_replacement]
-- </vc-theorems>
