-- <vc-preamble>
def Graph := List (List Nat)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_all_paths (g: Graph) : List (List Nat) :=
sorry

def is_valid_dag (g: Graph) : Bool :=
sorry

def verify_paths (g: Graph) (paths: List (List Nat)) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem paths_start_end_valid (g: Graph) (paths: List (List Nat))
  (h: paths = find_all_paths g) (h2: is_valid_dag g = true) :
  ∀ p ∈ paths, p.head? = some 0 ∧
               p.getLast? = some (g.length - 1) :=
sorry

theorem paths_follow_edges (g: Graph) (paths: List (List Nat))
  (h: paths = find_all_paths g) (h2: is_valid_dag g = true) :
  ∀ p ∈ paths, ∀ i < p.length - 1,
    (p.get! (i+1)) ∈ (g.get! (p.get! i)) :=
sorry

theorem paths_are_unique (g: Graph) (paths: List (List Nat))
  (h: paths = find_all_paths g) (h2: is_valid_dag g = true) :
  ∀ p₁ ∈ paths, ∀ p₂ ∈ paths, p₁ = p₂ ∨ p₁ ≠ p₂ :=
sorry

theorem linear_graph_single_path (n: Nat) (h: n ≥ 2) :
  let g : Graph := List.map (fun i => if i < n-1 then [i+1] else []) (List.range n)
  let paths := find_all_paths g
  paths.length = 1 ∧ paths.head? = some (List.range n) :=
sorry

theorem complete_dag_valid_paths (n: Nat) (h: n ≥ 3) :
  let g : Graph := List.map (fun i => List.filter (fun j => j > i ∧ j < n) (List.range n)) (List.range n)
  let paths := find_all_paths g
  verify_paths g paths = true :=
sorry
-- </vc-theorems>