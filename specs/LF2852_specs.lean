-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mul_power (n k : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem mul_power_perfect_power (n k : Nat) (h1: n > 0) (h2: k > 0) : 
  ∃ m : Nat, ∃ r : Nat, n * (mul_power n k) = r^k 
  := by sorry

theorem mul_power_k_one (n : Nat) (h: n > 0) : 
  mul_power n 1 = 1 
  := by sorry

theorem mul_power_n_one (k : Nat) (h: k > 0) :
  mul_power 1 k = 1
  := by sorry

theorem mul_power_perfect_square :
  mul_power 4 2 = 1 ∧ mul_power 9 2 = 1
  := by sorry

theorem mul_power_perfect_cube :
  mul_power 8 3 = 1 ∧ mul_power 27 3 = 1
  := by sorry
-- </vc-theorems>