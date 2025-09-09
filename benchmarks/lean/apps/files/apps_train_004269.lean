-- <vc-helpers>
-- </vc-helpers>

def binomial_sum_coefficients (n : Nat) : List Nat := sorry

theorem binomial_sum_coefficients_length (n : Nat) :
  (binomial_sum_coefficients n).length = n + 2 := sorry

theorem binomial_sum_coefficients_first (n : Nat) :
  (binomial_sum_coefficients n).head! = 1 := sorry

theorem binomial_sum_coefficients_powers_of_two (n : Nat) (i : Nat) :
  i ≤ n → 
  (binomial_sum_coefficients n).get! i = 2^i := sorry

theorem binomial_sum_coefficients_last (n : Nat) :
  (binomial_sum_coefficients n).getLast! = 2^(n+1) - 1 := sorry

/-
info: [1, 1]
-/
-- #guard_msgs in
-- #eval binomial_sum_coefficients 0

/-
info: [1, 2, 3]
-/
-- #guard_msgs in
-- #eval binomial_sum_coefficients 1

/-
info: [1, 2, 4, 8, 15]
-/
-- #guard_msgs in
-- #eval binomial_sum_coefficients 3

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible