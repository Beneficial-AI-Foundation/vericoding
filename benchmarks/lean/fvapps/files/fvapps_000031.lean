-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_ski_time (path: String) : Nat :=
  sorry

variable (path path1 path2 : String)

-- Time should always be positive
-- </vc-definitions>

-- <vc-theorems>
theorem ski_time_positive : 
  calculate_ski_time path > 0 := 
  sorry

-- Time is at least path length

theorem ski_time_lower_bound :
  calculate_ski_time path ≥ path.length := 
  sorry

-- Time is at most path length * 5

theorem ski_time_upper_bound :
  calculate_ski_time path ≤ path.length * 5 := 
  sorry

-- Concatenated paths are bounded by sum of individual path times

theorem ski_time_composition_bound :
  calculate_ski_time (path1 ++ path2) ≤ calculate_ski_time path1 + calculate_ski_time path2 :=
  sorry

-- Edge cases

theorem north_direction_time :
  calculate_ski_time "N" = 5 :=
  sorry

theorem north_south_time : 
  calculate_ski_time "NS" = 6 :=
  sorry
-- </vc-theorems>