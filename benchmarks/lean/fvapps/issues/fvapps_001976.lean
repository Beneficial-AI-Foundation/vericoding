-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_maze (n: Nat) (queries: List Query) : List String := sorry

theorem solve_maze_output_length (n: Nat) (queries: List Query) 
  (h: ∀ q ∈ queries, q.col ≤ n ∧ q.row ≤ 2) :
  queries ≠ [] → List.length (solve_maze n queries) = List.length queries := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_maze_valid_responses (n: Nat) (queries: List Query) 
  (h: ∀ q ∈ queries, q.col ≤ n ∧ q.row ≤ 2) :
  ∀ r ∈ solve_maze n queries, r = "Yes" ∨ r = "No" := sorry

theorem solve_maze_first_yes (n: Nat) (queries: List Query) 
  (h: ∀ q ∈ queries, q.col ≤ n ∧ q.row ≤ 2)
  (h2: queries ≠ []) :
  List.head! (solve_maze n queries) = "Yes" := sorry

theorem solve_maze_empty (n: Nat) :
  solve_maze n [] = [] := sorry
-- </vc-theorems>