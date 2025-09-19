-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Graph := (Nat × Nat × List (Nat × Nat))

def solve_graph_matching : List Graph → List (String × List Nat) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_vertex_empty_edges (g : Graph) (h : g = (1, 0, [])) :
  let result := solve_graph_matching [g]
  result.length = 1 ∧
  (result.head!).1 ∈ ["Matching", "IndSet"] ∧
  (result.head!).2.length = 1 := sorry

theorem single_edge (g : Graph) (h : g = (1, 1, [(1,2)])) :
  let result := solve_graph_matching [g]
  result.length = 1 ∧
  (result.head!).1 ∈ ["Matching", "IndSet"] ∧ 
  (result.head!).2.length = 1 := sorry

theorem two_vertex_one_edge (g : Graph) (h : g = (2, 1, [(1,2)])) :
  let result := solve_graph_matching [g]
  result.length = 1 ∧
  (result.head!).1 ∈ ["Matching", "IndSet"] ∧
  (result.head!).2.length = 2 := sorry

theorem matching_vertices_valid (g : Graph) (result : String × List Nat) :
  result ∈ solve_graph_matching [g] →
  result.1 = "Matching" →
  (∀ x, x ∈ result.2 → 1 ≤ x ∧ x ≤ g.2.1) ∧
  (∀ x y, x ∈ result.2 → y ∈ result.2 → x = y ∨ x ≠ y) := sorry

theorem indset_vertices_valid (g : Graph) (result : String × List Nat) :
  result ∈ solve_graph_matching [g] →
  result.1 = "IndSet" →
  (∀ x, x ∈ result.2 → 1 ≤ x ∧ x ≤ 3 * g.1) ∧
  (∀ x y, x ∈ result.2 → y ∈ result.2 → x = y ∨ x ≠ y) ∧
  ∀ v1 v2, v1 ∈ result.2 → v2 ∈ result.2 → v1 < v2 →
    ¬(v1, v2) ∈ (g.2.2.map (fun e => (min e.1 e.2, max e.1 e.2))) := sorry

theorem star_graph_has_indset (n : Nat) (edges : List (Nat × Nat)) :
  edges = List.map (fun i => (1, i+2)) (List.range n) →
  let result := (solve_graph_matching [(n, edges.length, edges)]).head!
  result.1 = "IndSet" ∧
  result.2.length = n := sorry
-- </vc-theorems>