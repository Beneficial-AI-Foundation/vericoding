def sort (as : List Nat) : List Nat := sorry

def countMismatches (xs ys : List Nat) : Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

def height_checker (heights : List Nat) : Nat := sorry

theorem height_checker_singleton (x : Nat) :
  height_checker [x] = 0 := sorry

theorem height_checker_uniform (x n : Nat) :
  n > 0 →
  height_checker (List.replicate n x) = 0 := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval height_checker [1, 1, 4, 2, 1, 3]

/-
info: 5
-/
-- #guard_msgs in
-- #eval height_checker [5, 1, 2, 3, 4]

/-
info: 0
-/
-- #guard_msgs in
-- #eval height_checker [1, 2, 3, 4, 5]

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible