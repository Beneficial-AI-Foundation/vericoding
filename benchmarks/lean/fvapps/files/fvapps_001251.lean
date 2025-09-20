-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def fibonacci_sum (n k : Nat) : Nat := sorry

def MOD := 1000000007
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>