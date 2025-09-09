-- <vc-helpers>
-- </vc-helpers>

def pathFinder (maze : String) : Option Nat := sorry

theorem path_finder_result_exists (maze : String) :
  ∃ (result : Option Nat), pathFinder maze = result := by sorry

theorem path_finder_empty_path :
  pathFinder "...\n...\n..." ≠ none := by sorry

theorem path_finder_blocked_two_by_two :
  pathFinder "W.\n.W" = none := by sorry

theorem path_finder_all_blocked_except_ends :
  pathFinder ".WW\nWWW\nWW." = none := by sorry

/- Any valid path length must be non-negative -/

theorem path_finder_positive_length (maze : String) (n : Nat) :
  pathFinder maze = some n → n > 0 := by sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval path_finder ".W.\n    .W.\n    ...".replace("    ", "")

/-
info: False
-/
-- #guard_msgs in
-- #eval path_finder ".W.\n    .W.\n    .W.".replace("    ", "")

/-
info: 4
-/
-- #guard_msgs in
-- #eval path_finder "...\n    ...\n    ...".replace("    ", "")

-- Apps difficulty: interview
-- Assurance level: unguarded