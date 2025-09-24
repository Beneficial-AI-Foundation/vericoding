-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (a b : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_number_returns_zero (n : Nat) : 
  n > 0 → solve n (n + 1) = 0 :=
  sorry

theorem solve_returns_natural {a b : Nat} :
  a > 0 → b > 0 → a ≤ b → solve a b ≥ 0 :=
  sorry

theorem empty_range_returns_zero {a b : Nat} :
  a > 0 → b > 0 → a > b → solve a b = 0 :=
  sorry

theorem result_less_than_range_sum {a b : Nat} :
  a > 0 → b > 0 → a < b → solve a b ≤ (b * (b - 1) / 2 - a * (a - 1) / 2) :=
  sorry

theorem solve_idempotent {a b : Nat} :
  a > 0 → b > 0 → solve a b = solve a b :=
  sorry

theorem solve_known_case :
  solve 1 100 = 6 :=
  sorry
-- </vc-theorems>