-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_chocolate_distribution (n k : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem chocolate_distribution_bounds {n k : Nat} (n_pos : n > 0):
  let result := solve_chocolate_distribution n k
  result ≥ 0 ∧ result ≤ 2*n-1
  := sorry

theorem zero_chocolates {n : Nat} (n_pos : n > 0):
  solve_chocolate_distribution n 0 = 0
  := sorry 

theorem perfect_distribution {n : Nat} (n_pos : n > 0):
  ∀ m : Nat, solve_chocolate_distribution n (n * m) = 0
  := sorry

theorem edge_cases_bounds :
  ∀ n k : Nat,
  n > 0 →
  let result := solve_chocolate_distribution n k
  result ≥ 0 ∧ result ≤ 2*n-1
  := sorry
-- </vc-theorems>