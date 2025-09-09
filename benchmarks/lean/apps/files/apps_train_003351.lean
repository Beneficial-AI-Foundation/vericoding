-- <vc-helpers>
-- </vc-helpers>

def apple (x : Int) : String := sorry

theorem apple_output_valid (x : Int) :
  apple x = "It's hotter than the sun!!" ∨ 
  apple x = "Help yourself to a honeycomb Yorkie for the glovebox." :=
sorry

theorem apple_squared_condition (x : Int) :
  (x * x > 1000) = (apple x = "It's hotter than the sun!!") := 
sorry

/-
info: "It's hotter than the sun!!"
-/
-- #guard_msgs in
-- #eval apple "50"

/-
info: 'Help yourself to a honeycomb Yorkie for the glovebox.'
-/
-- #guard_msgs in
-- #eval apple 4

/-
info: "It's hotter than the sun!!"
-/
-- #guard_msgs in
-- #eval apple 60

-- Apps difficulty: introductory
-- Assurance level: unguarded