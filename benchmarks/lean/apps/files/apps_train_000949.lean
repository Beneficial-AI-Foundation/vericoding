-- <vc-helpers>
-- </vc-helpers>

def arrange_particles (n : Nat) : Nat := sorry

theorem arrange_particles_base_cases :
  arrange_particles 0 = 1 ∧ arrange_particles 1 = 1 := sorry

theorem arrange_particles_known_values :
  arrange_particles 0 = 1 ∧ 
  arrange_particles 1 = 1 ∧
  arrange_particles 2 = 2 ∧
  arrange_particles 3 = 4 ∧
  arrange_particles 4 = 6 := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval arrange_particles 0

/-
info: 1
-/
-- #guard_msgs in
-- #eval arrange_particles 1

/-
info: 2
-/
-- #guard_msgs in
-- #eval arrange_particles 2

/-
info: 4
-/
-- #guard_msgs in
-- #eval arrange_particles 3

/-
info: 6
-/
-- #guard_msgs in
-- #eval arrange_particles 4

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible