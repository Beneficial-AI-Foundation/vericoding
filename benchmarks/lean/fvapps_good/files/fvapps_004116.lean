-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (a b : Nat) : Nat × Nat :=
  sorry

#check solve
-- </vc-definitions>

-- <vc-theorems>
theorem solve_returns_non_negative {a b : Nat} : 
  let result := solve a b
  result.1 ≥ 0 ∧ result.2 ≥ 0 := by 
  sorry

theorem solve_reduces_max {a b : Nat} :
  let result := solve a b 
  max result.1 result.2 ≤ max a b := by
  sorry 

theorem solve_final_state {a b : Nat} :
  let result := solve a b
  result.1 > 0 ∧ result.2 > 0 →
  result.1 < 2 * result.2 ∧ result.2 < 2 * result.1 := by
  sorry

theorem solve_zero_input {a b : Nat} :
  a = 0 ∨ b = 0 →
  solve a b = (a, b) := by
  sorry
-- </vc-theorems>