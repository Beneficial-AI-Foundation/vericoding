-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def IsBreakEven (costPrice : Int) (sellingPrice : Int) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem IsBreakEven_spec (costPrice sellingPrice : Int) :
costPrice ≥ 0 ∧ sellingPrice ≥ 0 →
IsBreakEven costPrice sellingPrice = (costPrice = sellingPrice) :=
sorry
-- </vc-theorems>