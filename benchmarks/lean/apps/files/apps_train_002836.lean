-- <vc-helpers>
-- </vc-helpers>

def pascal (n : Nat) : List (List Nat) := sorry

theorem pascal_row_count {n : Nat} (h : n > 0) : 
  List.length (pascal n) = n := sorry

/-
info: [[1]]
-/
-- #guard_msgs in
-- #eval pascal 1

/-
info: [[1], [1, 1], [1, 2, 1], [1, 3, 3, 1], [1, 4, 6, 4, 1]]
-/
-- #guard_msgs in
-- #eval pascal 5

/-
info: [[1], [1, 1], [1, 2, 1]]
-/
-- #guard_msgs in
-- #eval pascal 3

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible