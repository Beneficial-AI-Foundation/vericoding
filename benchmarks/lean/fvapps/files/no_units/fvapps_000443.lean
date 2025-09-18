-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def minCost (houses : List Nat) (cost : List (List Nat)) (m n target : Nat) : Int := sorry

theorem min_cost_non_negative 
  (houses : List Nat) (cost : List (List Nat)) (m n target : Nat) :
  let result := minCost houses cost m n target
  result = -1 ∨ result ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_cost_precolored
  (houses : List Nat) (cost : List (List Nat)) (m n target : Nat)
  (h : ∀ h ∈ houses, h > 0) :
  let neighborhoods := 
    (List.zip houses (List.drop 1 houses)).foldl
      (fun acc (p : Nat × Nat) => if p.1 ≠ p.2 then acc + 1 else acc) 1
  neighborhoods ≠ target → minCost houses cost m n target = -1 := sorry

theorem min_cost_deterministic
  (houses : List Nat) (cost : List (List Nat)) (m n target : Nat) :
  minCost houses cost m n target = minCost houses cost m n target := sorry

theorem min_cost_single_house_empty
  (cost : List (List Nat)) :
  minCost [0] [[1]] 1 1 1 = 1 := sorry

theorem min_cost_single_house_colored :
  minCost [1] [[1]] 1 1 1 = 0 := sorry

theorem min_cost_impossible_target :
  minCost [0,0] [[1,1], [1,1]] 2 2 3 = -1 := sorry
-- </vc-theorems>