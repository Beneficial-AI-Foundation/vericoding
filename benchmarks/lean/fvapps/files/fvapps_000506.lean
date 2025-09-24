-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_non_periodic_strings (n : Nat) (m : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_result_bounds (n m : Nat) 
  (h1 : n ≥ 2) (h2 : n ≤ 10000) (h3 : m > 0) (h4 : m ≤ 1000000000) :
  let result := solve_non_periodic_strings n m
  result ≥ 0 ∧ result < m ∧ result < 2^n :=
  sorry

theorem solve_small_n (n m : Nat)
  (h1 : 2 ≤ n) (h2 : n ≤ 4) (h3 : m = 1000000000) :
  let result := solve_non_periodic_strings n m
  result > 0 ∧ result ≤ 2^n - 2 :=
  sorry

theorem solve_n_one (m : Nat) (h : m > 0) :
  solve_non_periodic_strings 1 m = 1 :=
  sorry
-- </vc-theorems>