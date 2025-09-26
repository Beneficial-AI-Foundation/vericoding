-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_power_sum (a b c d : Nat) : Nat := sorry

theorem power_sum_nonneg (a b c d : Nat) : 
  calculate_power_sum a b c d ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem power_sum_is_powers (a b c d : Nat) :
  calculate_power_sum a b c d = a^b + c^d := sorry

theorem power_sum_symmetry (x n : Nat) :
  calculate_power_sum x n x n = 2 * x^n := sorry  

theorem power_sum_with_zero_right (a b c : Nat) :
  calculate_power_sum a b c 0 = a^b + 1 := sorry

theorem power_sum_with_zero_mid (a b c : Nat) :
  calculate_power_sum a 0 c b = 1 + c^b := sorry
-- </vc-theorems>