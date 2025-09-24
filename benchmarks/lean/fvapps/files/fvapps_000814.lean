-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_maze_path (n m : Nat) : String := sorry

theorem solve_maze_path_valid_result (n m : Nat) :
  n > 0 → m > 0 →
  solve_maze_path n m = "Yes" ∨ solve_maze_path n m = "No" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_maze_path_2x1 (m : Nat) :
  m > 0 →
  n * m = 2 →
  solve_maze_path n m = "Yes" := sorry

theorem solve_maze_path_single_dimension (n m : Nat) :
  n > 0 → m > 0 →
  (n = 1 ∨ m = 1) →
  n * m > 2 →
  solve_maze_path n m = "No" := sorry

theorem solve_maze_path_even_cells (n m : Nat) :
  n > 1 → m > 1 →
  (n * m) % 2 = 0 →
  solve_maze_path n m = "Yes" := sorry

theorem solve_maze_path_odd_cells (n m : Nat) :
  n > 0 → m > 0 →
  (n * m) % 2 = 1 →
  solve_maze_path n m = "No" := sorry

theorem solve_maze_path_square (n : Nat) :
  n > 0 →
  solve_maze_path n n = "Yes" ↔ (n > 1 ∧ (n * n) % 2 = 0) := sorry
-- </vc-theorems>