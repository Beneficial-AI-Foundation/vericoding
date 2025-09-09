-- <vc-helpers>
-- </vc-helpers>

def countNumbersWithUniqueDigits (n : Nat) : Nat := sorry

theorem countNumbersWithUniqueDigits_positive (n : Nat) :
  countNumbersWithUniqueDigits n > 0 := sorry

theorem countNumbersWithUniqueDigits_monotonic (n : Nat) :
  n > 0 → countNumbersWithUniqueDigits n ≥ countNumbersWithUniqueDigits (n-1) := sorry

theorem countNumbersWithUniqueDigits_plateau (n : Nat) :
  n ≥ 10 → countNumbersWithUniqueDigits n = countNumbersWithUniqueDigits 10 := sorry

theorem countNumbersWithUniqueDigits_zero :
  countNumbersWithUniqueDigits 0 = 1 := sorry

theorem countNumbersWithUniqueDigits_one :
  countNumbersWithUniqueDigits 1 = 10 := sorry

/-
info: 91
-/
-- #guard_msgs in
-- #eval count_numbers_with_unique_digits 2

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_numbers_with_unique_digits 0

/-
info: 10
-/
-- #guard_msgs in
-- #eval count_numbers_with_unique_digits 1

-- Apps difficulty: interview
-- Assurance level: guarded