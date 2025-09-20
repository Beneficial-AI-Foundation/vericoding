-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (count ball : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_in_range (count : Nat) (ball : Nat) (h : count > 0) : 
  solve count ball % count < count := by
  sorry

theorem solve_uniqueness (count : Nat) (h : count > 0) :
  ∀ b₁ b₂ : Nat, b₁ < count → b₂ < count → b₁ ≠ b₂ → solve count b₁ ≠ solve count b₂ := by
  sorry

theorem solve_deterministic (count ball : Nat) (h : count > 0) :
  solve count ball = solve count ball := by
  sorry

theorem solve_exists_output (count : Nat) (h : count > 0) :
  ∃ res : Nat, res = solve count 0 ∧ res < count := by
  sorry

theorem solve_specific_examples :
  solve 4 1 = 3 ∧ 
  solve 4 2 = 2 ∧
  solve 20 8 = 17 := by
  sorry
-- </vc-theorems>