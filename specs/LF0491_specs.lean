-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_malware_spread (graph : List (List Nat)) (initial : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_malware_spread_result_in_initial {graph : List (List Nat)} {initial : List Nat} 
    (h_graph_valid : List.length graph > 0)
    (h_initial_valid : List.length initial > 0)
    (h_initial_bounded : ∀ x, x ∈ initial → x < List.length graph)
    : min_malware_spread graph initial ∈ initial := 
  sorry

theorem min_malware_spread_minimum_node {graph : List (List Nat)} {initial : List Nat}
    (h_graph_valid : List.length graph > 0) 
    (h_initial_valid : List.length initial > 0)
    (h_initial_bounded : ∀ x, x ∈ initial → x < List.length graph)
    : ∀ x, x ∈ initial → min_malware_spread graph initial ≤ x := 
  sorry

theorem graph_symmetry {graph : List (List Nat)}
    (h_graph_valid : List.length graph > 0)
    : ∀ i j, i < List.length graph → j < List.length graph →
      (List.get! graph i).get! j = (List.get! graph j).get! i :=
  sorry

theorem graph_self_connections {graph : List (List Nat)}
    (h_graph_valid : List.length graph > 0)
    : ∀ i, i < List.length graph → (List.get! graph i).get! i = 1 :=
  sorry

theorem graph_binary_adjacency {graph : List (List Nat)}
    (h_graph_valid : List.length graph > 0)
    : ∀ i j, i < List.length graph → j < List.length graph →
      (List.get! graph i).get! j ≤ 1 :=
  sorry
-- </vc-theorems>