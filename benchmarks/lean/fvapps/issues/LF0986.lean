-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def List.sum (xs : List Nat) : Nat := sorry

def must_work_weekends (hours : List Nat) (productivity : Nat) : Bool := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem must_work_weekends_returns_bool (hours : List Nat) (productivity : Nat) :
  must_work_weekends hours productivity = true ∨ must_work_weekends hours productivity = false := sorry

theorem zero_hours_no_weekends (productivity : Nat) :
  must_work_weekends [0,0,0,0,0] productivity = false := sorry

theorem increasing_productivity_monotone (hours : List Nat) (productivity : Nat) :
  productivity > 0 →
  must_work_weekends hours productivity = true →
  must_work_weekends hours (productivity + 1) = true := sorry

theorem zero_productivity_no_weekends (hours : List Nat) :
  must_work_weekends hours 0 = false := sorry
-- </vc-theorems>