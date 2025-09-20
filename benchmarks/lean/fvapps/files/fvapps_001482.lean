-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def MOD : Nat := 10^9 + 7

def solve_prime_sum (n: Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_prime_sum_output_range (n: Nat) :
  solve_prime_sum n < MOD :=
sorry

theorem solve_prime_sum_deterministic (n: Nat) :
  solve_prime_sum n = solve_prime_sum n :=
sorry

theorem solve_prime_sum_monotone_init :
  solve_prime_sum 1 < solve_prime_sum 2 :=
sorry
-- </vc-theorems>