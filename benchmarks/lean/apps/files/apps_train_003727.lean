def digSum (n : Nat) (p : Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def digPow (n : Nat) (p : Nat) : Int :=
  sorry

theorem digPow_valid_result {n p : Nat} (h : digPow n p ≠ -1) :
  digSum n p = (digPow n p).toNat * n ∧ digPow n p > 0 := by
  sorry

theorem digPow_is_int (n p : Nat) :
  ∃ k : Int, digPow n p = k := by
  sorry

theorem digPow_power_one (n : Nat) :
  digSum n 1 % n = 0 →
  digPow n 1 = (digSum n 1) / n := by
  sorry

theorem digPow_power_one_neg (n : Nat) :
  digSum n 1 % n ≠ 0 →
  digPow n 1 = -1 := by
  sorry

theorem digPow_single_digit_power_one (n : Nat) :
  n > 0 → n < 10 →
  digPow n 1 = 1 := by
  sorry

theorem digPow_large_power_is_int (n p : Nat) :
  ∃ k : Int, digPow n p = k := by
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval dig_pow 89 1

/-
info: -1
-/
-- #guard_msgs in
-- #eval dig_pow 92 1

/-
info: 2
-/
-- #guard_msgs in
-- #eval dig_pow 695 2

-- Apps difficulty: introductory
-- Assurance level: guarded