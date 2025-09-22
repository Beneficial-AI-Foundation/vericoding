-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def total_n_queens (n: Nat) : Nat := sorry 

theorem total_n_queens_nonneg (n: Nat) : 
  total_n_queens n ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem total_n_queens_unique :
  ∀ n₁ n₂, 
  n₁ = n₂ → total_n_queens n₁ = total_n_queens n₂ := sorry
-- </vc-theorems>