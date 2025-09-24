-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def divide (weight : Int) : Bool := sorry

theorem divide_is_bool (weight : Int) :
  divide weight = true ∨ divide weight = false := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem divide_true_implies_conditions (weight : Int) :
  divide weight = true → weight > 2 ∧ weight % 2 = 0 := sorry

theorem divide_false_implies_conditions (weight : Int) : 
  divide weight = false → weight ≤ 2 ∨ weight % 2 ≠ 0 := sorry

theorem divide_positive_cases (weight : Int) (h1 : weight > 2) (h2 : weight % 2 = 0) :
  divide weight = true := sorry

theorem divide_negative_cases (weight : Int) (h : weight ≤ 2 ∨ weight % 2 ≠ 0) :
  divide weight = false := sorry
-- </vc-theorems>