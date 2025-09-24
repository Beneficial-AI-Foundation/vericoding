-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
-- </vc-definitions>

-- <vc-theorems>
theorem empty_graph_theorem (n : Nat) (degrees : List Int) :
  n > 0 →
  degrees.length ≤ n →
  List.Mem (1 : Int) degrees →
  solve_graph_subset n 0 degrees [] = [(0:Nat)] := sorry

theorem empty_graph_valid_theorem (n : Nat) (degrees : List Int) :
  n > 0 → 
  degrees.length ≤ n →
  ¬List.Mem (1 : Int) degrees →
  solve_graph_subset n 0 degrees [] = [] := sorry

theorem valid_solution_edges_theorem (n m : Nat) (degrees : List Int) (edges : List (Nat × Nat)) :
  n ≥ 2 →
  degrees.length = n →
  edges.length = m →
  (∀ (e : Nat × Nat), List.Mem e edges → e.1 ≠ e.2) →
  (∀ (e : Nat × Nat), List.Mem e edges → e.1 ≤ n ∧ e.2 ≤ n) →
  List.Nodup edges →
  let result := solve_graph_subset n m degrees edges
  result ≠ [(0:Nat)] →
  (∀ e, List.Mem e result → e ≤ m ∧ e ≥ 1) ∧ List.Nodup result := sorry

/-
info: -1
-/
-- #guard_msgs in
-- #eval solve_graph_subset 1 0 [1] []

/-
info: []
-/
-- #guard_msgs in
-- #eval solve_graph_subset 4 5 [0, 0, 0, -1] [(1, 2), (2, 3), (3, 4), (1, 4), (2, 4)]

/-
info: [1]
-/
-- #guard_msgs in
-- #eval solve_graph_subset 2 1 [1, 1] [(1, 2)]
-- </vc-theorems>