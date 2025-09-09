-- <vc-helpers>
-- </vc-helpers>

def nth_chandos_number (n : Nat) : Nat :=
  sorry

theorem small_known_values :
  nth_chandos_number 1 = 5 ∧
  nth_chandos_number 2 = 25 ∧
  nth_chandos_number 9 = 630 :=
  sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval nth_chandos_number 1

/-
info: 25
-/
-- #guard_msgs in
-- #eval nth_chandos_number 2

/-
info: 630
-/
-- #guard_msgs in
-- #eval nth_chandos_number 9

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible