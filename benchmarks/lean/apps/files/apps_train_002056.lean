-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_finite_fraction (p q b : Int) : Bool := sorry

theorem sign_invariance (p q b : Int) 
  (h1: q ≠ 0) (h2: b > 0) :
  is_finite_fraction p q b = is_finite_fraction (-p) q b := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem finite_power_of_two (p power : Int)
  (h1: p > 0) (h2: power > 0) :
  let nat_power := Int.toNat power
  is_finite_fraction p (Int.pow 2 nat_power) 10 = true := sorry 

theorem finite_power_of_five (p power : Int)
  (h1: p > 0) (h2: power > 0) : 
  let nat_power := Int.toNat power
  is_finite_fraction p (Int.pow 5 nat_power) 10 = true := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval is_finite_fraction 6 12 10

/-
info: False
-/
-- #guard_msgs in
-- #eval is_finite_fraction 4 3 10

/-
info: True
-/
-- #guard_msgs in
-- #eval is_finite_fraction 1 1 2

/-
info: True
-/
-- #guard_msgs in
-- #eval is_finite_fraction 9 36 2

/-
info: True
-/
-- #guard_msgs in
-- #eval is_finite_fraction 4 12 3

/-
info: False
-/
-- #guard_msgs in
-- #eval is_finite_fraction 3 5 4

/-
info: False
-/
-- #guard_msgs in
-- #eval is_finite_fraction 1 864691128455135232 2
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: unguarded