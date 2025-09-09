-- <vc-helpers>
-- </vc-helpers>

def total_n_queens (n: Nat) : Nat := sorry 

theorem total_n_queens_nonneg (n: Nat) : 
  total_n_queens n ≥ 0 := sorry

theorem total_n_queens_unique :
  ∀ n₁ n₂, 
  n₁ = n₂ → total_n_queens n₁ = total_n_queens n₂ := sorry

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible