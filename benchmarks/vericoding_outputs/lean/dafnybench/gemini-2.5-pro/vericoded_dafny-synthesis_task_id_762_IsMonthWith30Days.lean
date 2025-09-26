import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def IsMonthWith30Days (month : Int) : Bool :=
[4, 6, 9, 11].contains month
-- </vc-definitions>

-- <vc-theorems>
theorem IsMonthWith30Days_spec (month : Int) :
1 ≤ month ∧ month ≤ 12 →
IsMonthWith30Days month = (month = 4 ∨ month = 6 ∨ month = 9 ∨ month = 11) :=
by
  intro _
  simp [IsMonthWith30Days]
-- </vc-theorems>
