-- <vc-helpers>
-- </vc-helpers>

def eventual_safe_nodes (graph: List (List Nat)) : List Nat := sorry 

theorem eventual_safe_nodes_increasing {graph : List (List Nat)} : 
  ∀ i j, i < j → 
  let result := eventual_safe_nodes graph
  ∀ hi : i < result.length,
  ∀ hj : j < result.length,
  result[i]'hi ≤ result[j]'hj := sorry

theorem eventual_safe_nodes_valid_indices {graph : List (List Nat)} :
  ∀ x, x ∈ eventual_safe_nodes graph → x < graph.length := sorry

theorem eventual_safe_nodes_no_duplicates {graph : List (List Nat)} :
  ∀ x y, x ∈ eventual_safe_nodes graph → 
  y ∈ eventual_safe_nodes graph →
  x = y → x = y := sorry

theorem eventual_safe_nodes_contains_terminals {graph : List (List Nat)} :
  ∀ i h, graph[i]'h = [] →
  i ∈ eventual_safe_nodes graph := sorry

theorem eventual_safe_nodes_only_points_to_safe {graph : List (List Nat)} :
  ∀ node h, node ∈ eventual_safe_nodes graph →
  ∀ neighbor, neighbor ∈ graph[node]'h →
  neighbor ∈ eventual_safe_nodes graph := sorry

theorem eventual_safe_nodes_singleton_empty : 
  eventual_safe_nodes [List.nil] = [0] := sorry

theorem eventual_safe_nodes_singleton_self_loop :
  eventual_safe_nodes [[0]] = [] := sorry

/-
info: [2, 4, 5, 6]
-/
-- #guard_msgs in
-- #eval eventual_safe_nodes [[1, 2], [2, 3], [5], [0], [5], [], []]

/-
info: [0, 1, 2, 3, 4]
-/
-- #guard_msgs in
-- #eval eventual_safe_nodes [[], [0, 2, 3, 4], [3], [4], []]

/-
info: [4]
-/
-- #guard_msgs in
-- #eval eventual_safe_nodes [[1, 2, 3, 4], [1, 2], [3, 4], [0, 4], []]

-- Apps difficulty: interview
-- Assurance level: unguarded