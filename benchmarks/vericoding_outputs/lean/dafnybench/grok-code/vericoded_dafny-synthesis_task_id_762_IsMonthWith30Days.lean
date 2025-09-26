import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def IsMonthWith30Days (month : Int) : Bool :=
match month with
  | 4 => true
  | 6 => true
  | 9 => true
  | 11 => true
  | _ => false
-- </vc-definitions>

-- <vc-theorems>
theorem IsMonthWith30Days_spec (month : Int) :
1 ≤ month ∧ month ≤ 12 →
IsMonthWith30Days month = (month = 4 ∨ month = 6 ∨ month = 9 ∨ month = 11) :=
by unfold IsMonthWith30Days; by_cases h₁ : month = 4 <;> by_cases h₂ : month = 6 <;> by_cases h₃ : month = 9 <;> by_cases h₄ : month = 11 <;> simp [h₁, h₂, h₃, h₄]
-- </vc-theorems>
