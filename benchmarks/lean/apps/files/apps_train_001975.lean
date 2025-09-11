-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_cost_for_communication (n m : Nat) (lang_lists : List (List Nat)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem all_same_language (n m : Nat) (lang_lists : List (List Nat))
  (h1 : n = 5 ∧ m = 1)
  (h2 : lang_lists = [[1], [1], [1], [1], [1]]) :
  min_cost_for_communication n m lang_lists = 0 := sorry

theorem disjoint_groups (n m : Nat) (lang_lists : List (List Nat))
  (h1 : n = 4 ∧ m = 2) 
  (h2 : lang_lists = [[1], [1], [2], [2]]) :
  min_cost_for_communication n m lang_lists = 1 := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_cost_for_communication 5 5 [[2], [2, 3], [3, 4], [4, 5], [5]]

/-
info: 2
-/
-- #guard_msgs in
-- #eval min_cost_for_communication 8 7 [[], [1, 2, 3], [1], [5, 4], [6, 7], [3], [7, 4], [1]]

/-
info: 1
-/
-- #guard_msgs in
-- #eval min_cost_for_communication 2 2 [[2], []]
-- </vc-theorems>

-- Apps difficulty: competition
-- Assurance level: unguarded