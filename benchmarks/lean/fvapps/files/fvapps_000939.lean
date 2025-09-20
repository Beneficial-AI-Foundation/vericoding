-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_path_costs (n: Nat) (parents: List Nat) (values: List Nat) : List Nat :=
  sorry

def is_valid_tree (n: Nat) (parents: List Nat) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_length_matches_input
  (n: Nat) (values: List Nat) (parents: List Nat) :
  (n > 0) →
  (n > values.length → True) →
  (parents = List.replicate (n-1) 1) →
  (calculate_path_costs n parents (values.take n)).length = n :=
sorry

theorem path_costs_increase_with_depth
  (n: Nat) (parent_nodes: List Nat) (values: List Nat) :
  (n ≥ 2) →
  (parent_nodes.length = n-1) →
  (values.length ≥ n) →
  (is_valid_tree n parent_nodes = true) →
  ∀ i, i ≥ 1 → i < n →
    let result := calculate_path_costs n parent_nodes (values.take n)
    result.length = n →
    (i-1) < parent_nodes.length →
    parent_nodes[i-1]! - 1 < result.length →
    result[i]! ≥ result[parent_nodes[i-1]! - 1]! :=
sorry
-- </vc-theorems>