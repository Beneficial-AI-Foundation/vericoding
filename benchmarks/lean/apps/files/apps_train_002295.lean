def subtract_product_and_sum (n : Nat) : Int := sorry

def digits (n : Nat) : List Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

def product_of_list (l : List Nat) : Nat := sorry

def sum_of_list (l : List Nat) : Nat := sorry

theorem single_digit_zero (n : Nat) (h : n > 0 ∧ n < 10) :
  subtract_product_and_sum n = 0 := sorry

theorem three_digit_bounds (n : Nat) (h : n ≥ 100 ∧ n ≤ 999) :
  subtract_product_and_sum n ≤ 729 ∧ subtract_product_and_sum n ≥ -27 := sorry

/-
info: 15
-/
-- #guard_msgs in
-- #eval subtract_product_and_sum 234

/-
info: 21
-/
-- #guard_msgs in
-- #eval subtract_product_and_sum 4421

/-
info: -2
-/
-- #guard_msgs in
-- #eval subtract_product_and_sum 111

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible