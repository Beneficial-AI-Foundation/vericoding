-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_antimatching (n m : Nat) (edges : List (Nat × Nat)) : Nat :=
  sorry

def vertex_degree (v : Nat) (edges : List (Nat × Nat)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem antimatching_nonnegative (n m : Nat) (edges : List (Nat × Nat)) :
  solve_antimatching n m edges ≥ 0 :=
sorry

theorem antimatching_empty_graph (n : Nat) :
  solve_antimatching n 0 [] = 0 :=
sorry

theorem antimatching_single_vertex :
  solve_antimatching 1 0 [] = 0 :=
sorry

theorem antimatching_single_edge :
  solve_antimatching 2 1 [(1,2)] = 1 :=
sorry

theorem antimatching_triangle :
  solve_antimatching 3 3 [(1,2), (2,3), (1,3)] = 3 :=
sorry
-- </vc-theorems>