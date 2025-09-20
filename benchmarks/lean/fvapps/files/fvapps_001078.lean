-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_max_path_profits (n: Nat) (values: List Nat) (edges: List (Nat × Nat)) : Nat :=
  sorry

def is_valid_tree (n: Nat) (edges: List (Nat × Nat)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_node_case (n: Nat) (values: List Nat) :
  n = 1 → solve_max_path_profits n values [] = 0 := by
  sorry

theorem valid_inputs_result_properties (n: Nat) (values: List Nat) (edges: List (Nat × Nat)) :
  n ≥ 2 →
  values.length ≥ n →
  is_valid_tree n edges = true →
  let result := solve_max_path_profits n values edges
  (result ≥ 0 ∧ result ≤ 10^9 + 7) := by
  sorry

theorem line_graph_properties (n: Nat) (values: List Nat) :
  n ≥ 2 →
  values.length ≥ n →
  let edges := List.range (n-1) |>.map (fun i => (i+1, i+2))
  let result := solve_max_path_profits n values edges
  result ≥ 0 := by
  sorry
-- </vc-theorems>