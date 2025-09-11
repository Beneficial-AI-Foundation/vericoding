-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_paths (rows cols max_consecutive : Nat) (grid : List (List Nat)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_grid_zero_paths (max_consecutive : Nat) :
  find_paths 0 0 max_consecutive [] = 0 ∧
  find_paths 1 1 max_consecutive [] = 0 := by
  sorry

theorem single_cell_one_path (max_consecutive : Nat) 
  (h_max : 0 < max_consecutive) (h_max2 : max_consecutive ≤ 5) :
  find_paths 1 1 max_consecutive [[1]] = 1 := by
  sorry

theorem simple_path_bounds (max_consecutive : Nat)
  (h_max : 0 < max_consecutive) (h_max2 : max_consecutive ≤ 3) :
  let grid := [[1,1], [1,1]]
  let result := find_paths 2 2 max_consecutive grid
  0 < result ∧ result < 20011 := by
  sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval find_paths 3 4 2 [[1, 1, 1, 1], [0, 1, 1, 1], [1, 1, 1, 1]]

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_paths 2 2 1 [[1, 1], [1, 1]]

/-
info: 2
-/
-- #guard_msgs in
-- #eval find_paths 3 3 2 [[1, 1, 1], [1, 0, 1], [1, 1, 1]]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded