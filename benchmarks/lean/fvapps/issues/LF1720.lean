-- <vc-preamble>
def Graph.adjmat_2_graph {n : Nat} (g : Graph n) (mat : List (List Nat)) : List (String × List (String × Nat)) := sorry 
def Graph.graph_2_list {n : Nat} (g : Graph n) (graph : List (String × List (String × Nat))) : List (Nat × Nat × Nat) := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Graph.list_2_graph {n : Nat} (g : Graph n) (lst : List (Nat × Nat × Nat)) : List (String × List (String × Nat)) := sorry

theorem graph_initialization (size : Nat) (h : size > 0) : 
  ∃ g : Graph size, true 
  := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem adjmat_graph_properties {size : Nat} (h : size > 0) (mat : List (List Nat)) :
  ∀ g : Graph size,
  let graph := Graph.adjmat_2_graph g mat
  (∀ k ∈ graph, String.startsWith (k.fst) "A") ∧ 
  graph.length = size
  := sorry

theorem list_conversion_properties {size : Nat} (h : size > 0) (graph : List (String × List (String × Nat))) :
  ∀ g : Graph size,
  let lst := Graph.graph_2_list g graph
  let result := Graph.list_2_graph g lst
  (∀ k ∈ result, String.startsWith (k.fst) "A") ∧ 
  (∀ v ∈ result, v.snd.all (λ x => true))
  := sorry
-- </vc-theorems>