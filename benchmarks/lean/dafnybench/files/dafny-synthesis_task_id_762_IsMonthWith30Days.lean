-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def IsMonthWith30Days (month : Int) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem IsMonthWith30Days_spec (month : Int) :
1 ≤ month ∧ month ≤ 12 →
IsMonthWith30Days month = (month = 4 ∨ month = 6 ∨ month = 9 ∨ month = 11) :=
sorry
-- </vc-theorems>