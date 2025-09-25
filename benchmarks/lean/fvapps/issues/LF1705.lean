-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_puzzle (clues : List Nat) : Option Board :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solution_dimensions {clues : List Nat} {sol : Board} 
  (h : solve_puzzle clues = some sol) : 
  sol.rows.length = 4 ∧ ∀ row, row ∈ sol.rows → row.length = 4 :=
sorry

theorem solution_value_range {clues : List Nat} {sol : Board}
  (h : solve_puzzle clues = some sol) :
  ∀ row, row ∈ sol.rows → ∀ x, x ∈ row → 1 ≤ x ∧ x ≤ 4 :=
sorry 

theorem solution_row_uniqueness {clues : List Nat} {sol : Board}
  (h : solve_puzzle clues = some sol) :
  ∀ row, row ∈ sol.rows → 
  ∀ x y, x ∈ row → y ∈ row → x ≠ y → 
  List.indexOf x row ≠ List.indexOf y row :=
sorry

theorem solution_col_uniqueness {clues : List Nat} {sol : Board}
  (h : solve_puzzle clues = some sol) :
  ∀ i j : Nat, i < 4 → j < 4 → i ≠ j →
  ∀ col : List Nat, 
  (col = sol.rows.map (λ row => row[i]!)) →
  col[i]! ≠ col[j]! :=
sorry

/-
info: expected1
-/
-- #guard_msgs in
-- #eval solve_puzzle (2, 2, 1, 3, 2, 2, 3, 1, 1, 2, 2, 3, 3, 2, 1, 3)

/-
info: expected2
-/
-- #guard_msgs in
-- #eval solve_puzzle (0, 0, 1, 2, 0, 2, 0, 0, 0, 3, 0, 0, 0, 1, 0, 0)
-- </vc-theorems>