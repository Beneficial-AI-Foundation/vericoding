-- <vc-helpers>
-- </vc-helpers>

def powers_of_two (n : Nat) : List Nat := sorry

theorem powers_of_two_length (n : Nat) :
  (powers_of_two n).length = n + 1 := sorry

theorem powers_of_two_first_one (n : Nat) :
  (powers_of_two n).head! = 1 := sorry

/-
info: [1]
-/
-- #guard_msgs in
-- #eval powers_of_two 0

/-
info: [1, 2]
-/
-- #guard_msgs in
-- #eval powers_of_two 1

/-
info: [1, 2, 4, 8, 16]
-/
-- #guard_msgs in
-- #eval powers_of_two 4

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible