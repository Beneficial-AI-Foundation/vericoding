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
-- </vc-theorems>