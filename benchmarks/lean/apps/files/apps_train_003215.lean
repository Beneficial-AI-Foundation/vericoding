-- <vc-helpers>
-- </vc-helpers>

def is_even (n : Int) : Bool := sorry

theorem is_even_divisible_by_2 (n : Int) :
  is_even n = (n % 2 = 0) := sorry

theorem is_even_plus_2 (n : Int) :
  is_even n = is_even (n + 2) := sorry

theorem is_even_neighbor (n : Int) :
  is_even n ≠ is_even (n + 1) := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval is_even 2

/-
info: False
-/
-- #guard_msgs in
-- #eval is_even 3

/-
info: True
-/
-- #guard_msgs in
-- #eval is_even 14

-- Apps difficulty: introductory
-- Assurance level: unguarded