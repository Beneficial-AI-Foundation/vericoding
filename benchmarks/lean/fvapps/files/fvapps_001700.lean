-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def pathFinder (maze : String) : Option Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem path_finder_result_exists (maze : String) :
  ∃ (result : Option Nat), pathFinder maze = result := by
sorry

theorem path_finder_empty_path :
  pathFinder "...\n...\n..." ≠ none := by
sorry

theorem path_finder_blocked_two_by_two :
  pathFinder "W.\n.W" = none := by
sorry

theorem path_finder_all_blocked_except_ends :
  pathFinder ".WW\nWWW\nWW." = none := by
sorry

theorem path_finder_positive_length (maze : String) (n : Nat) :
  pathFinder maze = some n → n > 0 := by
sorry
-- </vc-theorems>