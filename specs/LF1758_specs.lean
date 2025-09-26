-- <vc-preamble>
def reachable_nodes (edges : List Edge) (M : Nat) (N : Nat) : Nat :=
  sorry

def isValidEdgeList (edges : List Edge) (N : Nat) : Bool :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sumWeights (edges : List Edge) : Nat :=
  edges.foldl (fun acc e => acc + e.2.2) 0
-- </vc-definitions>

-- <vc-theorems>
theorem reachable_nodes_basic_properties 
  {edges : List Edge} {M N : Nat}
  (h1 : 2 ≤ N) (h2 : N ≤ 10)
  (h3 : 1 ≤ M) (h4 : M ≤ 20)
  (h5 : isValidEdgeList edges N = true) :
  let result := reachable_nodes edges M N
  let total_intermediate := sumWeights edges
  (0 ≤ result) ∧ 
  (result ≤ N + total_intermediate) ∧
  (1 ≤ result) :=
sorry

theorem empty_graph_reaches_one
  {M N : Nat}
  (h1 : 0 ≤ M) (h2 : M ≤ 20)
  (h3 : 1 ≤ N) (h4 : N ≤ 10) :
  reachable_nodes ([] : List Edge) M N = 1 :=
sorry

theorem single_edge_properties
  {N w : Nat}
  (h1 : 2 ≤ N) (h2 : N ≤ 10)
  (h3 : 0 ≤ w) (h4 : w ≤ 20) :
  let edges := [(0, 1, w)]
  let M := w + 1
  let result := reachable_nodes edges M N
  (result ≤ 2 + w) ∧ (1 ≤ result) :=
sorry

/-
info: 13
-/
-- #guard_msgs in
-- #eval reachable_nodes [[0, 1, 10], [0, 2, 1], [1, 2, 2]] 6 3

/-
info: 23
-/
-- #guard_msgs in
-- #eval reachable_nodes [[0, 1, 4], [1, 2, 6], [0, 2, 8], [1, 3, 1]] 10 4
-- </vc-theorems>