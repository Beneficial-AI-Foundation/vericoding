-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_graph_cover (test_cases : List (Nat × Nat × List (Nat × Nat))) : 
  List (Nat × List Nat) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem graph_cover_size_matches_vertices {n m : Nat} {edges : List (Nat × Nat)}
  {result_size : Nat} {result_vertices : List Nat} :
  solve_graph_cover [(n,m,edges)] = [(result_size, result_vertices)] →
  result_size = result_vertices.length := sorry

theorem graph_cover_vertices_valid {n m : Nat} {edges : List (Nat × Nat)}
  {result_size : Nat} {result_vertices : List Nat} :
  solve_graph_cover [(n,m,edges)] = [(result_size, result_vertices)] →
  ∀ v ∈ result_vertices, 1 ≤ v ∧ v ≤ n := sorry

theorem graph_cover_vertices_no_duplicates {n m : Nat} {edges : List (Nat × Nat)}
  {result_size : Nat} {result_vertices : List Nat} :
  solve_graph_cover [(n,m,edges)] = [(result_size, result_vertices)] →
  ∀ x ∈ result_vertices, ∀ y ∈ result_vertices, x = y → 
  result_vertices.indexOf x = result_vertices.indexOf y := sorry

theorem graph_cover_size_bound {n m : Nat} {edges : List (Nat × Nat)}
  {result_size : Nat} {result_vertices : List Nat} :
  solve_graph_cover [(n,m,edges)] = [(result_size, result_vertices)] →
  result_size ≤ (n + 1) / 2 := sorry

theorem minimal_graph_cover {result_size : Nat} {result_vertices : List Nat} :
  solve_graph_cover [(2, 1, [(1,2)])] = [(result_size, result_vertices)] →
  result_size = 1 := sorry
-- </vc-theorems>