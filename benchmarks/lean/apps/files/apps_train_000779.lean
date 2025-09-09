-- <vc-helpers>
-- </vc-helpers>

def count_solved_problems (N: Nat) (confidence_matrix: List (List Nat)) : Nat :=
sorry

theorem count_solved_problems_non_negative {N: Nat} {confidence_matrix: List (List Nat)} :
  count_solved_problems N confidence_matrix ≥ 0 :=
sorry

theorem count_solved_problems_upper_bound {N: Nat} {confidence_matrix: List (List Nat)} :
  count_solved_problems N confidence_matrix ≤ confidence_matrix.length :=
sorry

theorem count_solved_problems_matches_confident {N: Nat} {confidence_matrix: List (List Nat)} :
  count_solved_problems N confidence_matrix = 
    (confidence_matrix.filter (fun conf => (conf.foldl (· + ·) 0) ≥ 2)).length :=
sorry

theorem count_solved_problems_empty {N: Nat} :
  count_solved_problems N [] = 0 :=
sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval count_solved_problems 3 [[1, 1, 0], [1, 1, 1], [1, 0, 0]]

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_solved_problems 4 [[1, 1, 1], [0, 0, 0], [1, 1, 0], [0, 1, 1]]

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_solved_problems 2 [[0, 0, 0], [1, 0, 0]]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible