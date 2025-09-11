-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_power_of_four (n: Int) : Bool 
  := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem is_power_of_four_if_true {n : Int} (h : is_power_of_four n = true) : 
  n > 0 := sorry

theorem is_power_of_four_negative {n : Int} (h : n ≤ 0) : 
  is_power_of_four n = false := sorry

theorem is_power_of_four_exp {n : Nat} :
  is_power_of_four (4^n) = true := sorry

theorem is_power_of_four_power_two {n : Nat} (h : n ≥ 2) :
  is_power_of_four (2^n) = (n % 2 = 0) := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval is_power_of_four 16

/-
info: False
-/
-- #guard_msgs in
-- #eval is_power_of_four 5

/-
info: True
-/
-- #guard_msgs in
-- #eval is_power_of_four 64
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded