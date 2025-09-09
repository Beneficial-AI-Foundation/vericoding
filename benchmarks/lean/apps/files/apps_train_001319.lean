def solve_tourist_spots (n : Nat) (roads : List String) : Float :=
sorry

-- <vc-helpers>
-- </vc-helpers>

def isValidRoad : String → Bool :=
sorry

theorem solve_tourist_spots_output_is_float (n : Nat) (roads : List String) 
    (h : n ≥ 2) (h2 : roads.length > 0) :
  ∃ (f : Float), solve_tourist_spots n roads = f :=
sorry

theorem solve_tourist_spots_total_weight 
    {n : Nat} {roads : List String} {weights : List Float}
    (h : n ≥ 2)
    (h2 : roads.length > 0) 
    (h3 : weights = roads.map (fun r => sorry)) :
  solve_tourist_spots n roads ≤ weights.foldl (. + .) 0.0 :=
sorry

theorem solve_tourist_spots_invalid_input
    {n : Nat} {roads : List String}
    (h : n ≥ 2)
    (h2 : ∃ r ∈ roads, ¬ isValidRoad r) :
  solve_tourist_spots n roads = 0.0 :=
sorry

-- Apps difficulty: interview
-- Assurance level: guarded