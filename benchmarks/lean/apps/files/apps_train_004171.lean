-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def you_are_a_cube (n : Nat) : Bool := sorry

theorem cubes_identified_correctly (n : Nat) :
  let cube_root := n^(1/3)
  you_are_a_cube n = (cube_root^3 = n) :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem explicit_cubes_true (n : Nat) :
  you_are_a_cube (n * n * n) = true :=
sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval you_are_a_cube 27

/-
info: True
-/
-- #guard_msgs in
-- #eval you_are_a_cube 1

/-
info: False
-/
-- #guard_msgs in
-- #eval you_are_a_cube 2

/-
info: False
-/
-- #guard_msgs in
-- #eval you_are_a_cube 99

/-
info: True
-/
-- #guard_msgs in
-- #eval you_are_a_cube 64
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded