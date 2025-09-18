-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_valid_parent_array (n: Nat) (p: List Nat) : Bool := sorry

def solve_graph_assignment (n: Nat) (p: List Nat) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem odd_cycle_impossible (n: Nat) (h1: 2 ≤ n) (h2: n % 2 = 1) : 
  let p := (List.range (n-1)).map (λ x => x + 2) ++ [1]
  solve_graph_assignment n p = "IMPOSSIBLE" := sorry

theorem even_cycle_possible (n: Nat) (h1: 2 ≤ n) (h2: n % 2 = 0) :
  let p := (List.range (n-1)).map (λ x => x + 2) ++ [1]
  solve_graph_assignment n p = "POSSIBLE" := sorry

theorem valid_output_format (n: Nat) (p: List Nat) (h1: 2 ≤ n) :
  is_valid_parent_array n p →
  (solve_graph_assignment n p = "POSSIBLE" ∨ solve_graph_assignment n p = "IMPOSSIBLE") := sorry

theorem consistent_result (n: Nat) (p: List Nat) (h1: 2 ≤ n) :
  is_valid_parent_array n p →
  solve_graph_assignment n p = solve_graph_assignment n p := sorry
-- </vc-theorems>