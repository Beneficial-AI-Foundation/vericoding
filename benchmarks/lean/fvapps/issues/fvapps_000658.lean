-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isValidDate (d : Date) : Bool := sorry

def get_day_for_date (day month year : Nat) : Option Weekday := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem get_day_for_date_valid_output 
  {day month year : Nat}
  (h1: 1 ≤ day ∧ day ≤ 31)
  (h2: 1 ≤ month ∧ month ≤ 12) 
  (h3: 1 ≤ year ∧ year ≤ 9999)
  (h4: isValidDate ⟨day, month, year⟩ = true) :
  ∃ w : Weekday, get_day_for_date day month year = some w :=
sorry

theorem get_day_for_date_invalid_dates :
  get_day_for_date 31 2 2023 = none :=
sorry

theorem get_day_for_date_invalid_zero
  {day month year : Nat}
  (h1: day = 0 ∨ month = 0) :
  get_day_for_date day month year = none :=
sorry

/-
info: 'Wednesday'
-/
-- #guard_msgs in
-- #eval get_day_for_date 14 3 2012

/-
info: 'Saturday'
-/
-- #guard_msgs in
-- #eval get_day_for_date 1 1 2000

/-
info: 'Monday'
-/
-- #guard_msgs in
-- #eval get_day_for_date 25 12 2023
-- </vc-theorems>