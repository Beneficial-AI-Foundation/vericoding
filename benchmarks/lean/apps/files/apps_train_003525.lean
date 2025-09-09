-- <vc-helpers>
-- </vc-helpers>

def find_deleted_number (arr : List Int) (mixed : List Int) : Int :=
  sorry

theorem empty_arrays : 
  find_deleted_number [] [] = 0 :=
sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval find_deleted_number [1, 2, 3, 4, 5, 6, 7, 8, 9] [5, 7, 9, 4, 8, 1, 2, 3]

/-
info: 0
-/
-- #guard_msgs in
-- #eval find_deleted_number [1, 2, 3, 4, 5, 6, 7] [2, 3, 6, 1, 5, 4, 7]

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_deleted_number [1] []

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible