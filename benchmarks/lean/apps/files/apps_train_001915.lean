-- <vc-helpers>
-- </vc-helpers>

def solve_codefortia (n m a b : Nat) (edges : List (Nat × Nat × Nat)) : List Nat := sorry

theorem solve_codefortia_result_length {n m a b : Nat} {edges : List (Nat × Nat × Nat)} :
  (solve_codefortia n m a b edges).length = n :=
sorry

theorem solve_codefortia_start_vertex {n m a b : Nat} {edges : List (Nat × Nat × Nat)} :
  n ≥ 1 → List.get! (solve_codefortia n m a b edges) 0 = 0 :=
sorry 

theorem solve_codefortia_distances_nonneg {n m a b : Nat} {edges : List (Nat × Nat × Nat)} :
  ∀ x ∈ solve_codefortia n m a b edges, x ≥ 0 :=
sorry

theorem solve_codefortia_min_graph_props {edges : List (Nat × Nat × Nat)} :
  edges.length = 1 →
  (∀ (u v w : Nat), (u,v,w) ∈ edges → u ≤ 2 ∧ v ≤ 2 ∧ w ≤ 2) →
  let result := solve_codefortia 2 1 1 2 edges
  result.length = 2 ∧ 
  List.get! result 0 = 0 ∧
  ∀ x ∈ result, x ≥ 0 :=
sorry

/-
info: [0, 25, 60, 40, 20]
-/
-- #guard_msgs in
-- #eval solve_codefortia 5 5 20 25 [(1, 2, 25), (2, 3, 25), (3, 4, 20), (4, 5, 20), (5, 1, 20)]

/-
info: [0, 13, 26, 39, 26, 13]
-/
-- #guard_msgs in
-- #eval solve_codefortia 6 7 13 22 [(1, 2, 13), (2, 3, 13), (1, 4, 22), (3, 4, 13), (4, 5, 13), (5, 6, 13), (6, 1, 13)]

/-
info: [0, 1]
-/
-- #guard_msgs in
-- #eval solve_codefortia 2 1 1 2 [(2, 1, 1)]

-- Apps difficulty: competition
-- Assurance level: unguarded