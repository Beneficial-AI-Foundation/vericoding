-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (lists : List (List Int)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_positive (lists : List (List Int)) :
  solve lists ≥ 1 := by
  sorry

theorem solve_equals_product_unique (lists : List (List Int)) :
  solve lists = lists.foldl (fun acc l => acc * (l.eraseDups).length) 1 := by
  sorry

theorem solve_empty_list :
  solve [] = 1 := by
  sorry 

theorem solve_single_list (lst : List Int) :
  solve [lst] = (lst.eraseDups).length := by
  sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval solve [[1, 2], [4], [5, 6]]

/-
info: 4
-/
-- #guard_msgs in
-- #eval solve [[1, 2], [4, 4], [5, 6, 6]]

/-
info: 72
-/
-- #guard_msgs in
-- #eval solve [[1, 2, 3], [3, 4, 6, 6, 7], [8, 9, 10, 12, 5, 6]]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded