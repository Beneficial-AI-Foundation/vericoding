-- <vc-helpers>
-- </vc-helpers>

def last_digit (n1 : Nat) (n2 : Nat) : Nat :=
  sorry

theorem last_digit_range (n1 n2 : Nat) : 
  last_digit n1 n2 ≤ 9 
  ∧ last_digit n1 n2 ≥ 0 :=
sorry

theorem last_digit_zero_exp (n1 : Nat) :
  last_digit n1 0 = 1 :=
sorry

theorem last_digit_power_one (n1 : Nat) :
  last_digit n1 1 = n1 % 10 :=
sorry 

theorem last_digit_powers_of_ten (n1 n2 : Nat) :
  n1 % 10 = 0 ∧ n2 > 0 → last_digit n1 n2 = 0 :=
sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval last_digit 4 1

/-
info: 6
-/
-- #guard_msgs in
-- #eval last_digit 4 2

/-
info: 9
-/
-- #guard_msgs in
-- #eval last_digit 9 7

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible