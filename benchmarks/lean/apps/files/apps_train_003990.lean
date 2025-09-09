def maximum : List Nat → Nat 
  | [] => 0
  | (x::xs) => max x (maximum xs)

def minimum : List Nat → Nat
  | [] => 0
  | (x::xs) => min x (minimum xs)

-- <vc-helpers>
-- </vc-helpers>

def largest_rect (heights : List Nat) : Nat :=
  sorry

theorem largest_rect_empty :
  largest_rect [] = 0 :=
  sorry

/-
info: 16
-/
-- #guard_msgs in
-- #eval largest_rect [3, 5, 12, 4, 10]

/-
info: 12
-/
-- #guard_msgs in
-- #eval largest_rect [6, 2, 5, 4, 5, 1, 6]

/-
info: 70
-/
-- #guard_msgs in
-- #eval largest_rect [33, 9, 7, 6, 6, 6, 14, 14, 14, 15, 21]

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible