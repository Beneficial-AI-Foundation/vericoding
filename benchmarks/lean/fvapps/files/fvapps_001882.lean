-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Edge := List Int
def max_removable_edges (n : Int) (edges : List Edge) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_edges_result {n : Int} (hn : n ≥ 0) :
  max_removable_edges n [] = if n = 0 then 0 else -1 :=
  sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval max_removable_edges 4 [[3, 1, 2], [3, 2, 3], [1, 1, 3], [1, 2, 4], [1, 1, 2], [2, 3, 4]]

/-
info: 0
-/
-- #guard_msgs in
-- #eval max_removable_edges 4 [[3, 1, 2], [3, 2, 3], [1, 1, 4], [2, 1, 4]]

/-
info: -1
-/
-- #guard_msgs in
-- #eval max_removable_edges 4 [[3, 2, 3], [1, 1, 2], [2, 3, 4]]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible