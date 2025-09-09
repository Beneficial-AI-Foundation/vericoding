-- <vc-helpers>
-- </vc-helpers>

def cup_and_balls (b : Nat) (swaps : List (List Nat)) : Nat := sorry

theorem empty_swaps_preserves_position {b : Nat}
  (h1 : b > 0) (h2 : b ≤ 100) :
  cup_and_balls b [] = b := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval cup_and_balls 2 [[1, 2]]

/-
info: 1
-/
-- #guard_msgs in
-- #eval cup_and_balls 1 [[2, 3], [1, 2], [1, 2]]

/-
info: 3
-/
-- #guard_msgs in
-- #eval cup_and_balls 2 [[1, 3], [1, 2], [2, 1], [2, 3]]

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible