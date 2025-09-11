-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_operations (logs : List String) : Nat := sorry

theorem depth_never_negative (logs : List String) : 
  min_operations logs ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem up_directory_at_root (logs : List String) :
  min_operations ("../" :: logs) = min_operations logs := sorry

theorem current_directory_neutral (logs : List String) :
  min_operations logs = min_operations (logs ++ ["./"])  := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval min_operations ["d1/", "d2/", "../", "d21/", "./"]

/-
info: 3
-/
-- #guard_msgs in
-- #eval min_operations ["d1/", "d2/", "./", "d3/", "../", "d31/"]

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_operations ["d1/", "../", "../", "../"]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible