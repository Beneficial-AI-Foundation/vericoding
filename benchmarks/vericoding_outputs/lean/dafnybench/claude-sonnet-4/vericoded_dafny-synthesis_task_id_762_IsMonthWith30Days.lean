import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: No additional helpers needed for this implementation
-- </vc-helpers>

-- <vc-definitions>
def IsMonthWith30Days (month : Int) : Bool :=
if month = 4 ∨ month = 6 ∨ month = 9 ∨ month = 11 then true else false
-- </vc-definitions>

-- <vc-theorems>
theorem IsMonthWith30Days_spec (month : Int) :
1 ≤ month ∧ month ≤ 12 →
IsMonthWith30Days month = (month = 4 ∨ month = 6 ∨ month = 9 ∨ month = 11) :=
by
  intro h
  unfold IsMonthWith30Days
  simp only [Bool.cond_eq_ite, Bool.ite_eq_true_distrib]
  split_ifs with h_cond
  · simp [h_cond]
  · simp [h_cond]
-- </vc-theorems>
