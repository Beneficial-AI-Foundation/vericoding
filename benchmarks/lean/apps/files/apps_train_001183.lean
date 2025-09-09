def Edge := Nat × Nat × Nat
def Graph := List Edge

-- <vc-helpers>
-- </vc-helpers>

def count_shortest_paths (n : Nat) (edges : Graph) : Nat :=
  sorry

theorem count_paths_positive 
  (n : Nat) (edges : Graph) 
  (h1 : n ≥ 2)
  (h2 : edges.length > 0) :
  count_shortest_paths n edges > 0 := 
  sorry

theorem count_paths_permutation_invariant
  (n : Nat) (edges1 edges2 : Graph)
  (h : edges2 = edges1) :
  count_shortest_paths n edges1 = count_shortest_paths n edges2 :=
  sorry

theorem count_paths_weight_order_invariant
  (n : Nat) (edges edges_rev : Graph)
  (h : edges_rev = edges) :
  count_shortest_paths n edges = count_shortest_paths n edges_rev :=
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_shortest_paths 3 [(1, 2, 3), (2, 3, 6), (1, 3, 7)]

/-
info: 2
-/
-- #guard_msgs in
-- #eval count_shortest_paths 3 [(1, 2, 3), (2, 3, 6), (1, 3, 9)]

-- Apps difficulty: interview
-- Assurance level: unguarded