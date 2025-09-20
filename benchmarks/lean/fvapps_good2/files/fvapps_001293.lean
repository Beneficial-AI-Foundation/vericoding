-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_largest_n (k : Nat) : Nat :=
  sorry

def count_steps_to_zero (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_largest_n_returns_valid (k : Nat) (h : k > 0) (h2 : k ≤ 1000) :
  find_largest_n k ≥ 0 :=
sorry

theorem find_largest_n_edge_cases :
  find_largest_n 1 = 0 ∧
  find_largest_n 2 = 9 ∧
  find_largest_n 3 = 10 :=
sorry
-- </vc-theorems>