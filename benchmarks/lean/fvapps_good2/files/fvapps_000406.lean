-- <vc-preamble>
def IsValidGraph (graph : List (List Nat)) : Prop :=
  graph ≠ [] ∧
  ∀ neighbors ∈ graph, ∀ x ∈ neighbors, x < graph.length
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def CatMouseGame (graph : List (List Nat)) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem cat_mouse_game_output_range (graph : List (List Nat)) :
  CatMouseGame graph = 0 ∨ CatMouseGame graph = 1 ∨ CatMouseGame graph = 2 :=
sorry

theorem cat_mouse_game_output_range_valid (graph : List (List Nat)) :
  IsValidGraph graph →
  CatMouseGame graph = 0 ∨ CatMouseGame graph = 1 ∨ CatMouseGame graph = 2 :=
sorry
-- </vc-theorems>