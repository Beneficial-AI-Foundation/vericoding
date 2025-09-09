-- <vc-helpers>
-- </vc-helpers>

def permutation_position (s : String) : Nat := sorry 

def position_to_perm (pos : Nat) : String := sorry

theorem permutation_position_positive (s : String) (h : s ≠ "") :
  permutation_position s > 0 := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval permutation_position "a"

/-
info: 26
-/
-- #guard_msgs in
-- #eval permutation_position "z"

/-
info: 3759
-/
-- #guard_msgs in
-- #eval permutation_position "foo"

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible