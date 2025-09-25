-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_negatives (grid : List (List Int)) : Nat := sorry

theorem count_negatives_matches_direct_count (grid : List (List Int)) : 
  count_negatives grid = (grid.bind (·.filter (·<0))).length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_negatives_nonnegative (grid : List (List Int)) :
  count_negatives grid ≥ 0 := sorry

/-
info: 8
-/
-- #guard_msgs in
-- #eval count_negatives [[4, 3, 2, -1], [3, 2, 1, -1], [1, 1, -1, -2], [-1, -1, -2, -3]]

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_negatives [[3, 2], [1, 0]]

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_negatives [[1, -1], [-1, -1]]
-- </vc-theorems>