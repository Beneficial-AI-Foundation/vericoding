-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_button_presses (a b : Int) : Int := sorry

theorem min_button_presses_non_negative (a b : Int) :
  min_button_presses a b ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_button_presses_equal_inputs (a : Int) :
  min_button_presses a a = 0 := sorry

theorem min_button_presses_symmetric (a b : Int) :
  min_button_presses a b = min_button_presses b a := sorry

theorem min_button_presses_sufficient (a b : Int) :
  min_button_presses a b * 5 ≥ (if a ≥ b then a - b else b - a) := sorry
-- </vc-theorems>