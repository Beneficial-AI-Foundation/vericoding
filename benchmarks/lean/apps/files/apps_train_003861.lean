-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def permutation_position (s : String) : Nat := sorry 

def position_to_perm (pos : Nat) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible