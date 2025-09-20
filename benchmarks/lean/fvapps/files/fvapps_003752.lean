-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def press_button (n : Int) : Int := sorry 

theorem press_button_positive_bounds {n : Int} (h : n > 0) (h2 : n ≤ 1000) :
  press_button n ≥ 0 ∧ press_button n ≤ n * n * n := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem press_button_non_positive (n : Int) (h : n ≤ 0) :
  press_button n = (n * n + 5) * n / 6 := sorry

theorem press_button_fixed_points :
  press_button 0 = 0 ∧ press_button 1 = 1 := sorry
-- </vc-theorems>