-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def remove_covered_intervals (intervals: List Interval) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem remove_covered_intervals_empty :
  remove_covered_intervals [] = 0 :=
  sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval remove_covered_intervals [[1, 4], [3, 6], [2, 8]]

/-
info: 1
-/
-- #guard_msgs in
-- #eval remove_covered_intervals [[1, 4], [2, 3]]

/-
info: 2
-/
-- #guard_msgs in
-- #eval remove_covered_intervals [[3, 10], [4, 10], [5, 11]]
-- </vc-theorems>