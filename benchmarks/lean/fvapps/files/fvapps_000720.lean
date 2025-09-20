-- <vc-preamble>
def Point := Nat × Nat -- Position representation
def Direction := String -- Direction representation
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def process : List String → String 
  | lst => sorry
-- </vc-definitions>

-- <vc-theorems>
theorem direction_valid (moves : List String) :
  let result := process moves
  ∃ d, d ∈ ["", "N", "S", "E", "W", "NE", "NW", "SE", "SW"] ∧ 
  (result.endsWith d ∨ result = "0.0") := by
  sorry

theorem distance_nonneg (moves : List String) :
  let result := process moves
  let numStr := result.take (result.length - 2)  -- Take all but direction
  (String.toNat! numStr) ≥ 0 := by
  sorry

theorem origin_return :
  process ["1", "R", "1", "R", "1", "R", "1"] = "0.0" := by
  sorry

theorem single_move (n : Nat) (h : 0 < n ∧ n ≤ 100) :
  process [toString n] = s!"{toString n}.0N" := by
  sorry

theorem distance_triangle_inequality (moves : List String) :
  let total_distance := moves.foldl (fun acc x => 
    if x ∉ ["L", "R"] then acc + (String.toNat! x) else acc) 0
  let result := process moves
  let resultNum := String.toNat! (result.take (result.length - 2))
  resultNum ≤ total_distance := by
  sorry
-- </vc-theorems>