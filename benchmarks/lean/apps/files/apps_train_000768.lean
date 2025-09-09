-- <vc-helpers>
-- </vc-helpers>

def sumFirstLastDigit (n : Nat) : Nat :=
  sorry

theorem sum_first_last_digit_in_range (n : Nat) (h : n > 0) :
  let result := sumFirstLastDigit n
  result ≥ 0 ∧ result ≤ 18
  := sorry

theorem single_digit_sum_is_double (n : Nat) (h1 : n > 0) (h2 : n ≤ 9) :
  sumFirstLastDigit n = n + n
  := sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval sum_first_last_digit 1234

/-
info: 5
-/
-- #guard_msgs in
-- #eval sum_first_last_digit 124894

/-
info: 5
-/
-- #guard_msgs in
-- #eval sum_first_last_digit 242323

-- Apps difficulty: interview
-- Assurance level: guarded