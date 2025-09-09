-- <vc-helpers>
-- </vc-helpers>

def is_triangle (a b c : Int) : Bool := sorry

theorem non_positive_sides_are_invalid {a b c : Int} :
  (a ≤ 0 ∨ b ≤ 0 ∨ c ≤ 0) → is_triangle a b c = false := sorry

theorem triangle_inequality {a b c : Int} : 
  is_triangle a b c = true → 
  (a < b + c ∧ b < a + c ∧ c < a + b) := sorry

theorem equilateral_triangle {side : Int} :
  side > 0 → is_triangle side side side = true := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval is_triangle 1 2 2

/-
info: False
-/
-- #guard_msgs in
-- #eval is_triangle 7 2 2

/-
info: False
-/
-- #guard_msgs in
-- #eval is_triangle 0 2 3

-- Apps difficulty: introductory
-- Assurance level: unguarded