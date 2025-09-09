/-
## Task

You are at position `[0, 0]` in maze NxN and you can **only** move in one of the four cardinal directions (i.e. North, East, South, West). Return the minimal number of steps to exit position `[N-1, N-1]` *if* it is possible to reach the exit from the starting position.  Otherwise, return `false` in **JavaScript**/**Python** and `-1` in **C++**/**C#**/**Java**.

Empty positions are marked `.`.  Walls are marked `W`.  Start and exit positions are guaranteed to be empty in all test cases.

## Path Finder Series:

-       [#1: can you reach the exit?](https://www.codewars.com/kata/5765870e190b1472ec0022a2)
-       [#2: shortest path](https://www.codewars.com/kata/57658bfa28ed87ecfa00058a)
-       [#3: the Alpinist](https://www.codewars.com/kata/576986639772456f6f00030c)
-       [#4: where are you?](https://www.codewars.com/kata/5a0573c446d8435b8e00009f)
-       [#5: there's someone here](https://www.codewars.com/kata/5a05969cba2a14e541000129)
-/

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