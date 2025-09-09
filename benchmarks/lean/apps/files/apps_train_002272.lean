-- <vc-helpers>
-- </vc-helpers>

def min_square_area (a b : Nat) : Nat := sorry

def sqrt (n : Nat) : Nat := sorry

theorem min_square_area_commutative (a b : Nat) (h : a > 0 ∧ b > 0) :
  min_square_area a b = min_square_area b a := sorry

/-
info: 16
-/
-- #guard_msgs in
-- #eval min_square_area 3 2

/-
info: 16
-/
-- #guard_msgs in
-- #eval min_square_area 4 2

/-
info: 40000
-/
-- #guard_msgs in
-- #eval min_square_area 100 100

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible