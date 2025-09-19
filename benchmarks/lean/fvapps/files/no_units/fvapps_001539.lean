-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_jumping_game (x y : Nat) : Nat × Nat := sorry

theorem result_valid {x y : Nat} :
  let (result, _) := solve_jumping_game x y
  result = 0 ∨ result = 1 ∨ result = 2 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem diff_nonneg {x y : Nat} :
  let (_, diff) := solve_jumping_game x y
  diff ≥ 0 := sorry

theorem result_zero_implies_diff_zero {x y : Nat} :
  let (result, diff) := solve_jumping_game x y
  result = 0 → diff = 0 := sorry

theorem symmetric_results {x y : Nat} :
  let (result1, diff1) := solve_jumping_game x y
  let (result2, diff2) := solve_jumping_game y x
  (result1 = 1 → result2 = 2) ∧
  (result1 = 2 → result2 = 1) ∧
  (result1 = 0 → result2 = 0) ∧
  diff1 = diff2 := sorry

theorem same_input_tie {x : Nat} :
  let (result, diff) := solve_jumping_game x x
  result = 0 ∧ diff = 0 := sorry
-- </vc-theorems>