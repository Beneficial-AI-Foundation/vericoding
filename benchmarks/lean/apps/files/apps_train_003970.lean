/-
Spin-off of this kata, here you will have to figure out an efficient strategy to solve the problem of finding the sole duplicate number among an unsorted array/list of numbers starting from 1 up to n.

Hints: a solution in linear time can be found; using the most intuitive ones to search for duplicates that can run in O(n²) time won't work.
-/

-- <vc-helpers>
-- </vc-helpers>

def find_dup (arr : List Nat) : Nat :=
  sorry

theorem find_dup_minimal :
  find_dup [1, 1] = 1 :=
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_dup [1, 1, 2, 3]

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_dup [1, 2, 2, 3]

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_dup [5, 4, 3, 2, 1, 1]

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible