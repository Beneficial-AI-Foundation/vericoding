-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def manhattan_distance (p1 p2 : List Int) : Int := sorry

def min_cost_connect_points (points : List (List Int)) : Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem min_cost_nonnegative (points : List (List Int)) :
  min_cost_connect_points points ≥ 0 := sorry

theorem single_point_cost (point : List Int) :
  min_cost_connect_points [point] = 0 := sorry

theorem cost_greater_than_max_distance (points : List (List Int)) :
  min_cost_connect_points points ≥ 
    (List.foldl (fun acc i =>
      List.foldl (fun acc' j =>
        max acc' (manhattan_distance (points.get! i) (points.get! j))) 
      acc
      (List.range (points.length)))
    0
    (List.range points.length)) := sorry

theorem cost_upper_bound (points : List (List Int)) (max_dist : Int) :
  min_cost_connect_points points ≤ max_dist * (points.length - 1) := sorry

theorem translation_invariance (points : List (List Int)) (dx dy : Int) :
  min_cost_connect_points points = 
    min_cost_connect_points (points.map (fun p => [p.get! 0 + dx, p.get! 1 + dy])) := sorry
-- </vc-theorems>