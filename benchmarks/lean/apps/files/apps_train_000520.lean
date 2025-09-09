def solve_antimatching (n m : Nat) (edges : List (Nat × Nat)) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def vertex_degree (v : Nat) (edges : List (Nat × Nat)) : Nat :=
  sorry

theorem antimatching_nonnegative (n m : Nat) (edges : List (Nat × Nat)) :
  solve_antimatching n m edges ≥ 0 := sorry

theorem antimatching_empty_graph (n : Nat) : 
  solve_antimatching n 0 [] = 0 := sorry

theorem antimatching_single_vertex :
  solve_antimatching 1 0 [] = 0 := sorry

theorem antimatching_single_edge :
  solve_antimatching 2 1 [(1,2)] = 1 := sorry

theorem antimatching_triangle :
  solve_antimatching 3 3 [(1,2), (2,3), (1,3)] = 3 := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve_antimatching 3 3 [(1, 2), (1, 3), (2, 3)]

/-
info: 1
-/
-- #guard_msgs in
-- #eval solve_antimatching 4 2 [(1, 2), (3, 4)]

/-
info: 0
-/
-- #guard_msgs in
-- #eval solve_antimatching 5 0 []

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible