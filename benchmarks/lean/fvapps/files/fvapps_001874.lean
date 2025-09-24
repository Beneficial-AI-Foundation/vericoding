-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def shortest_path (grid : List (List Nat)) (k : Nat) : Int := sorry

theorem shortest_path_result_valid (grid : List (List Nat)) (k : Nat) :
  shortest_path grid k ≥ -1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem shortest_path_with_sufficient_k 
  (grid : List (List Nat)) (k rows cols : Nat)
  (h₁ : grid.length = rows)
  (h₂ : ∀ row ∈ grid, row.length = cols)
  (h₃ : k ≥ rows + cols - 2) :
  let result := shortest_path grid k;
  -1 < result ∧ result ≤ rows + cols - 2 := sorry

theorem shortest_path_blocked_ends 
  (grid : List (List Nat)) 
  (h₁ : grid ≠ [])
  (h₂ : (∃ first ∈ grid, first ≠ [] ∧ first.head? = some 1) ∨ 
        (∃ last ∈ grid, last ≠ [] ∧ last.getLast? = some 1)) :
  shortest_path grid 0 = -1 := sorry

theorem shortest_path_min_length 
  (grid : List (List Nat)) (k rows cols : Nat)
  (h₁ : grid.length = rows)
  (h₂ : ∀ row ∈ grid, row.length = cols) :
  let result := shortest_path grid k;
  result ≠ -1 → result ≥ rows + cols - 2 := sorry

theorem shortest_path_empty_grid (rows cols : Nat) 
  (h₁ : rows > 0)
  (h₂ : cols > 0) :
  let empty_grid := List.replicate rows (List.replicate cols 0);
  shortest_path empty_grid 0 = rows + cols - 2 := sorry
-- </vc-theorems>