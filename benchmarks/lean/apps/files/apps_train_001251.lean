-- <vc-helpers>
-- </vc-helpers>

def fibonacci_sum (n k : Nat) : Nat := sorry

def MOD := 1000000007

theorem fibonacci_sum_bounds (n k : Nat) :
  fibonacci_sum n k < MOD := sorry

theorem fibonacci_sum_base_case : 
  fibonacci_sum 1 1 = 1 := sorry

theorem fibonacci_sum_mod_equiv (n k : Nat) :
  fibonacci_sum n k = fibonacci_sum n (k + MOD) := sorry

theorem fibonacci_sum_zero_k (n : Nat) :
  fibonacci_sum n 0 = 0 := sorry

theorem fibonacci_sum_negative_n_error (n : Int) (k : Nat) :
  n < 0 → fibonacci_sum (Int.toNat n) k = 0 := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval fibonacci_sum 1 1

/-
info: 2
-/
-- #guard_msgs in
-- #eval fibonacci_sum 1 2

-- Apps difficulty: interview
-- Assurance level: unguarded