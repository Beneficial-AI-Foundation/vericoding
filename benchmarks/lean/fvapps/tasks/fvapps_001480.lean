-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isValidTree (n : Nat) (edges : List (Nat × Nat)) : Bool :=
  sorry

def findOptimalAttack (n : Nat) (edges : List (Nat × Nat)) : Nat × Nat :=
  sorry

def getAdjList (n : Nat) (edges : List (Nat × Nat)) : List (List Nat) :=
  sorry

def componentSize (adj : List (List Nat)) (start visited : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_optimal_attack_output_bounds {n : Nat} {edges : List (Nat × Nat)}
  (h_valid : isValidTree n edges = true) :
  let (attack_node, max_subgraph) := findOptimalAttack n edges
  1 ≤ attack_node ∧ attack_node ≤ n ∧
  1 ≤ max_subgraph ∧ max_subgraph ≤ n-1 :=
sorry

theorem breaking_point_subgraph_sizes {n : Nat} {edges : List (Nat × Nat)}
  (h_valid : isValidTree n edges = true) :
  let (attack_node, max_subgraph) := findOptimalAttack n edges;
  let adj := getAdjList n edges;
  ∀ node neighbors, neighbors = (adj.get? (attack_node-1)).getD [] →
  node ∈ neighbors →
  componentSize adj [node] [attack_node] ≤ max_subgraph :=
sorry
-- </vc-theorems>