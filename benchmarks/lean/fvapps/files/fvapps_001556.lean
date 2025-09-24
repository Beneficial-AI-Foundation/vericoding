-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def who_is_winner (moves : List String) : String :=
  sorry

def columnHeight (moves : List String) (col : String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem valid_result_states (moves : List String) :
  let result := who_is_winner moves
  result = "Red" ∨ result = "Yellow" ∨ result = "Draw" := by
  sorry

theorem column_height_bound (moves : List String) (col : String) :
  columnHeight moves col ≤ 6 := by
  sorry
-- </vc-theorems>