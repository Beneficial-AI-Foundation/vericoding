-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def check_float (s : String) : Bool := sorry

theorem integers_invalid (n : Int) :
  check_float (toString n) = false := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem special_cases_invalid (s : String) :
  s = "" ∨ s = "." ∨ s = "1." ∨ s = "+." ∨ s = "-." ∨ 
  s = "inf" ∨ s = "-inf" ∨ s = "nan" ∨ s = "1e5" ∨ s = "1.2.3" →
  check_float s = false := sorry
-- </vc-theorems>