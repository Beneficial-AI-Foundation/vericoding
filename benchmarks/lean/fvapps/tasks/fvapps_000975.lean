-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_path_queries (N : Nat) (node_values : List Nat) (edges : List (Nat × Nat)) 
  (queries : List (Char × Nat × Nat)) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_path_queries_results_length {N : Nat} {node_values : List Nat} 
  {edges : List (Nat × Nat)} {queries : List (Char × Nat × Nat)} :
  List.length (solve_path_queries N node_values edges queries) = List.length queries :=
  sorry

theorem solve_path_queries_results_nonnegative {N : Nat} {node_values : List Nat}
  {edges : List (Nat × Nat)} {queries : List (Char × Nat × Nat)} :
  ∀ x ∈ solve_path_queries N node_values edges queries, x ≥ 0 :=
  sorry

theorem solve_path_queries_valid_tree {N : Nat} {node_values : List Nat} 
  {edges : List (Nat × Nat)} (h1 : N ≥ 2) (h2 : List.length edges = N - 1)
  (h3 : ∀ e ∈ edges, e.1 ≥ 1 ∧ e.1 < e.2 ∧ e.2 ≤ N) :
  True :=
  sorry

theorem solve_path_queries_valid_queries {N : Nat} {queries : List (Char × Nat × Nat)} 
  (h : ∀ q ∈ queries, (q.1 = 'C' ∨ q.1 = 'F') ∧ 
    q.2.1 ≥ 1 ∧ q.2.1 ≤ N ∧ 
    q.2.2 ≥ 1 ∧ q.2.2 ≤ N ∧
    q.2.1 ≠ q.2.2) :
  True :=
  sorry
-- </vc-theorems>