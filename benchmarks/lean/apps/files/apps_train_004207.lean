-- <vc-helpers>
-- </vc-helpers>

def middle_point (x1 y1 z1 x2 y2 z2 x3 y3 z3 : Float) : Nat := sorry

theorem middle_point_returns_valid_index (x1 y1 z1 x2 y2 z2 x3 y3 z3 : Float) :
  let result := middle_point x1 y1 z1 x2 y2 z2 x3 y3 z3
  result = 1 ∨ result = 2 ∨ result = 3 := sorry

theorem identical_points_return_middle_index (x y z : Float) :
  middle_point x y z x y z x y z = 2 := sorry 

theorem two_identical_points_first_not_third (x1 y1 z1 x2 y2 z2 : Float) :
  middle_point x1 y1 z1 x1 y1 z1 x2 y2 z2 ≠ 3 := sorry

theorem two_identical_points_last_not_first (x1 y1 z1 x2 y2 z2 : Float) :
  middle_point x1 y1 z1 x2 y2 z2 x2 y2 z2 ≠ 1 := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval middle_point 1 2 3 4 5 6 7 8 9

/-
info: 3
-/
-- #guard_msgs in
-- #eval middle_point 0 2 0 6 -2 8 3 0 4

/-
info: 3
-/
-- #guard_msgs in
-- #eval middle_point 0.25 0.5 0.75 3.25 -0.5 -0.25 1.0 0.25 0.5

-- Apps difficulty: introductory
-- Assurance level: unguarded