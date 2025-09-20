-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def apple (x : Int) : String := sorry

theorem apple_output_valid (x : Int) :
  apple x = "It's hotter than the sun!!" ∨ 
  apple x = "Help yourself to a honeycomb Yorkie for the glovebox." :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem apple_squared_condition (x : Int) :
  (x * x > 1000) = (apple x = "It's hotter than the sun!!") := 
sorry
-- </vc-theorems>