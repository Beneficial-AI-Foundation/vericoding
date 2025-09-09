-- <vc-helpers>
-- </vc-helpers>

def adjust (coin price : Int) : Int := sorry

theorem adjust_multiple (coin price : Int) (h : coin > 0) : 
  (adjust coin price) % coin = 0 := sorry

theorem adjust_greater_equal (coin price : Int) (h : coin > 0) :
  adjust coin price ≥ price := sorry

theorem adjust_minimal (coin price : Int) (h : coin > 0) :
  adjust coin price - coin < price := sorry

theorem adjust_idempotent (coin price : Int) (h : coin > 0) :
  adjust coin (adjust coin price) = adjust coin price := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval adjust 3 0

/-
info: 3
-/
-- #guard_msgs in
-- #eval adjust 3 1

/-
info: 0
-/
-- #guard_msgs in
-- #eval adjust 3 -2

/-
info: -3
-/
-- #guard_msgs in
-- #eval adjust 3 -4

/-
info: 3
-/
-- #guard_msgs in
-- #eval adjust 3 3

/-
info: 6
-/
-- #guard_msgs in
-- #eval adjust 3 6

/-
info: 9
-/
-- #guard_msgs in
-- #eval adjust 3 7

-- Apps difficulty: introductory
-- Assurance level: unguarded