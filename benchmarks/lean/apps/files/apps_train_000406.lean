-- <vc-preamble>
def CatMouseGame (graph : List (List Nat)) : Nat := sorry

/- For a valid graph input, the output is either 0, 1 or 2 -/
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def IsValidGraph (graph : List (List Nat)) : Prop :=
  graph ≠ [] ∧ 
  ∀ neighbors ∈ graph, ∀ x ∈ neighbors, x < graph.length

/- The cat-mouse game output range theorem only applies to valid graphs -/
-- </vc-definitions>

-- <vc-theorems>
theorem cat_mouse_game_output_range (graph : List (List Nat)) :
  CatMouseGame graph = 0 ∨ CatMouseGame graph = 1 ∨ CatMouseGame graph = 2 := sorry

/- A graph is valid if:
1. It is non-empty
2. Each node's neighbors are valid indices into the graph -/

theorem cat_mouse_game_output_range_valid (graph : List (List Nat)) :
  IsValidGraph graph →
  CatMouseGame graph = 0 ∨ CatMouseGame graph = 1 ∨ CatMouseGame graph = 2 := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval cat_mouse_game [[2, 5], [3], [0, 4, 5], [1, 4, 5], [2, 3], [0, 2, 3]]

/-
info: 0
-/
-- #guard_msgs in
-- #eval cat_mouse_game [[2, 5], [3], [0, 4, 5], [1, 4, 5], [2, 3], [0, 2, 3], [], []]

/-
info: 1
-/
-- #guard_msgs in
-- #eval cat_mouse_game [[1, 3], [0], [3], [0, 2]]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded