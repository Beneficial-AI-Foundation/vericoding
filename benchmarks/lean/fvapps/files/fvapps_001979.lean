-- <vc-preamble>
def list_max (xs : List Nat) : Nat :=
match xs with
| [] => 0
| (x::xs) => List.foldl Nat.max x xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def make_tree_edges (n : Nat) (edge_weights : List Nat) : List (Nat × Nat × Nat) :=
sorry

def solve (n : Nat) (weights : List Nat) (roads : List (Nat × Nat × Nat)) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_produces_nat (n : Nat) (weights : List Nat) (roads : List (Nat × Nat × Nat)) :
  solve n weights roads ≥ 0 :=
sorry

theorem solve_at_least_max_weight (n : Nat) (weights : List Nat) (roads : List (Nat × Nat × Nat))
  (h : weights ≠ []) :
  solve n weights roads ≥ list_max weights :=
sorry

theorem solve_singleton (w : Nat) :
  solve 1 [w] [] = w :=
sorry

theorem solve_small_cases (n : Nat) (weights : List Nat) (h₁ : n ≤ 3) (h₂ : weights.length = n)
  (h₃ : weights ≠ []) :
  let roads := List.map (fun i => (i + 1, i + 2, 1)) (List.range (n-1))
  solve n weights roads ≥ list_max weights :=
sorry
-- </vc-theorems>