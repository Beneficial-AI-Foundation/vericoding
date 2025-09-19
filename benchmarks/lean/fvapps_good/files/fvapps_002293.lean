-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def robotSim (commands : List Int) (obstacles : List (Int × Int)) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem robotSim_result_nonnegative (commands : List Int) (obstacles : List (Int × Int)) :
  robotSim commands obstacles ≥ 0 := 
  sorry

theorem robotSim_empty_commands (obstacles : List (Int × Int)) :
  robotSim [] obstacles = 0 :=
  sorry

theorem robotSim_no_obstacles_consistent (commands : List Int) :
  robotSim commands [] = robotSim commands [] :=
  sorry

theorem robotSim_obstacles_reduce_distance (commands : List Int) (obstacles : List (Int × Int)) :
  robotSim commands obstacles ≤ robotSim commands [] :=
  sorry

theorem robotSim_turns_only_zero (commands : List Int) (h : ∀ x ∈ commands, x = -1 ∨ x = -2) :
  robotSim commands [] = 0 :=
  sorry
-- </vc-theorems>