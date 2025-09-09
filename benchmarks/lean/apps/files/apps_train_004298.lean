-- <vc-helpers>
-- </vc-helpers>

def find_next_power (val : Nat) (pow : Nat) : Nat := sorry

theorem find_next_power_greater 
  (val : Nat) (pow : Nat)
  (h1 : val ≥ 1) (h2 : pow ≥ 2) (h3 : pow ≤ 8) :
  find_next_power val pow > val := sorry

/-
info: 13824
-/
-- #guard_msgs in
-- #eval find_next_power 12385 3

/-
info: 1419857
-/
-- #guard_msgs in
-- #eval find_next_power 1245678 5

/-
info: 1771561
-/
-- #guard_msgs in
-- #eval find_next_power 1245678 6

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible