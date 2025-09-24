-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def MonthHas31Days (month : Int) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem MonthHas31Days_spec (month : Int) :
1 ≤ month ∧ month ≤ 12 →
MonthHas31Days month = true ↔
(month = 1 ∨ month = 3 ∨ month = 5 ∨ month = 7 ∨
month = 8 ∨ month = 10 ∨ month = 12) :=
sorry
-- </vc-theorems>