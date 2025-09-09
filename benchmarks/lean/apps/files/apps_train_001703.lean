def valid_solution (board : List (List Nat)) : Bool := sorry

def check_unique_1_to_9 (arr : List Nat) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

def get_box_elements (board : List (List Nat)) (box_i box_j : Nat) : List Nat := sorry 

def get_column (board : List (List Nat)) (j : Nat) : List Nat := sorry

theorem valid_grid_properties (board : List (List Nat)) :
  (∀ row ∈ board, check_unique_1_to_9 row) ∧ 
  (∀ j, 0 ≤ j ∧ j < 9 → check_unique_1_to_9 (get_column board j)) ∧
  (∀ i j, 0 ≤ i ∧ i < 3 ∧ 0 ≤ j ∧ j < 3 → 
    check_unique_1_to_9 (get_box_elements board (3*i) (3*j)))
  → valid_solution board := sorry

theorem invalid_numbers (board : List (List Nat)) :
  (∃ row ∈ board, ∃ x ∈ row, x < 1 ∨ x > 9) →
  ¬ valid_solution board := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval valid_solution [[5, 3, 4, 6, 7, 8, 9, 1, 2], [6, 7, 2, 1, 9, 5, 3, 4, 8], [1, 9, 8, 3, 4, 2, 5, 6, 7], [8, 5, 9, 7, 6, 1, 4, 2, 3], [4, 2, 6, 8, 5, 3, 7, 9, 1], [7, 1, 3, 9, 2, 4, 8, 5, 6], [9, 6, 1, 5, 3, 7, 2, 8, 4], [2, 8, 7, 4, 1, 9, 6, 3, 5], [3, 4, 5, 2, 8, 6, 1, 7, 9]]

/-
info: False
-/
-- #guard_msgs in
-- #eval valid_solution [[5, 3, 4, 6, 7, 8, 9, 1, 2], [6, 7, 2, 1, 9, 0, 3, 4, 8], [1, 0, 0, 3, 4, 2, 5, 6, 0], [8, 5, 9, 7, 6, 1, 0, 2, 0], [4, 2, 6, 8, 5, 3, 7, 9, 1], [7, 1, 3, 9, 2, 4, 8, 5, 6], [9, 0, 1, 5, 3, 7, 2, 1, 4], [2, 8, 7, 4, 1, 9, 6, 3, 5], [3, 0, 0, 4, 8, 1, 1, 7, 9]]

-- Apps difficulty: interview
-- Assurance level: unguarded