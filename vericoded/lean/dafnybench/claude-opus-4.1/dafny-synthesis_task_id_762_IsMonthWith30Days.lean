import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- No additional helpers needed for this simple predicate
-- </vc-helpers>

-- <vc-definitions>
def IsMonthWith30Days (month : Int) : Bool :=
month = 4 || month = 6 || month = 9 || month = 11
-- </vc-definitions>

-- <vc-theorems>
theorem IsMonthWith30Days_spec (month : Int) :
1 ≤ month ∧ month ≤ 12 →
IsMonthWith30Days month = (month = 4 ∨ month = 6 ∨ month = 9 ∨ month = 11) :=
by
  intro h
  simp only [IsMonthWith30Days]
  -- Convert between Bool and Prop
  rw [Bool.or_eq_true, Bool.or_eq_true, Bool.or_eq_true]
  simp only [decide_eq_true_iff]
  -- The associativity of ∨ needs to be handled
  simp only [or_assoc]
-- </vc-theorems>
