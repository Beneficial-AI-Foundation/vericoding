-- <vc-helpers>
-- </vc-helpers>

def solve (a b : Nat) : Nat × Nat :=
  sorry

#check solve

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

/-
info: [6, 7]
-/
-- #guard_msgs in
-- #eval solve 6 19

/-
info: [0, 1]
-/
-- #guard_msgs in
-- #eval solve 2 1

/-
info: [7, 11]
-/
-- #guard_msgs in
-- #eval solve 7 11

-- Apps difficulty: introductory
-- Assurance level: unguarded