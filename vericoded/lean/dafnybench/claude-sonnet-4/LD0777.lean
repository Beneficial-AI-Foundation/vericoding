import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- No additional helpers needed for this simple implementation
-- </vc-helpers>

-- <vc-definitions>
def IsBreakEven (costPrice : Int) (sellingPrice : Int) : Bool :=
costPrice = sellingPrice
-- </vc-definitions>

-- <vc-theorems>
theorem IsBreakEven_spec (costPrice sellingPrice : Int) :
costPrice ≥ 0 ∧ sellingPrice ≥ 0 →
IsBreakEven costPrice sellingPrice = (costPrice = sellingPrice) :=
by
  intro h
  simp [IsBreakEven]
-- </vc-theorems>
