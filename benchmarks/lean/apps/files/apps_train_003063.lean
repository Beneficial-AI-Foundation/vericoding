def abs (n : Int) : Int :=
  if n ≥ 0 then n else -n

-- <vc-helpers>
-- </vc-helpers>

def get_sum (a b : Int) : Int := sorry

theorem get_sum_commutative (a b : Int) : 
  get_sum a b = get_sum b a := sorry

theorem get_sum_same_number (n : Int) :
  get_sum n n = n := sorry

theorem get_sum_consecutive (a b : Int) :
  a ≠ b → get_sum a b = ((a + b) / 2) * (abs (b - a) + 1) := sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval get_sum 1 3

/-
info: 2
-/
-- #guard_msgs in
-- #eval get_sum -1 2

/-
info: 5
-/
-- #guard_msgs in
-- #eval get_sum 5 5

-- Apps difficulty: introductory
-- Assurance level: unguarded