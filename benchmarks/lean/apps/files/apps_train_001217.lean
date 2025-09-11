-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_road_trips (n m k : Nat) (roads : List (Nat × Nat)) (museums : List Nat) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem zero_roads_k_gt_n {n k : Nat} (h : k > n) :
  solve_road_trips n 0 k [] (List.replicate n 0) = -1 := sorry

theorem zero_roads_k_leq_n {n k : Nat} (h : k ≤ n) :
  let result := solve_road_trips n 0 k [] (List.replicate n 0)
  ∃ x : Int, result = x ∧ result = 0 := sorry

/-
info: 345
-/
-- #guard_msgs in
-- #eval solve_road_trips 10 10 3 [(1, 3), (3, 5), (5, 1), (1, 6), (6, 2), (5, 6), (2, 5), (7, 10), (4, 7), (10, 9)] [20, 0, 15, 20, 25, 30, 30, 150, 35, 20]

/-
info: 240
-/
-- #guard_msgs in
-- #eval solve_road_trips 10 10 2 [(1, 3), (3, 5), (5, 1), (1, 6), (6, 2), (5, 6), (2, 5), (7, 10), (4, 7), (10, 9)] [20, 0, 15, 20, 25, 30, 30, 150, 35, 20]

/-
info: -1
-/
-- #guard_msgs in
-- #eval solve_road_trips 10 10 5 [(1, 3), (3, 5), (5, 1), (1, 6), (6, 2), (5, 6), (2, 5), (7, 10), (4, 7), (10, 9)] [20, 0, 15, 20, 25, 30, 30, 150, 35, 20]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded