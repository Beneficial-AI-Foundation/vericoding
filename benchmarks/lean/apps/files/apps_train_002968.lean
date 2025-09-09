-- <vc-helpers>
-- </vc-helpers>

def chess_triangle (n m : Int) : Int := sorry

theorem zero_dimensions :
  chess_triangle 0 1 = 0 ∧ 
  chess_triangle 1 0 = 0 ∧ 
  chess_triangle 0 0 = 0 := sorry

theorem tiny_boards :
  ∀ n m, n < 2 → m < 2 → chess_triangle n m = 0 := sorry

/-
info: 8
-/
-- #guard_msgs in
-- #eval chess_triangle 2 3

/-
info: 48
-/
-- #guard_msgs in
-- #eval chess_triangle 3 3

/-
info: 40
-/
-- #guard_msgs in
-- #eval chess_triangle 5 2

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible