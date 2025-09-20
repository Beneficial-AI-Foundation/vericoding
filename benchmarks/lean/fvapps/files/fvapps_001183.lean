-- <vc-preamble>
def Edge := Nat × Nat × Nat
def Graph := List Edge
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_shortest_paths (n : Nat) (edges : Graph) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>