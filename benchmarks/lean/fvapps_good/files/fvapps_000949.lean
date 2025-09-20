-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def arrange_particles (n : Nat) : Nat := sorry

theorem arrange_particles_base_cases :
  arrange_particles 0 = 1 ∧ arrange_particles 1 = 1 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem arrange_particles_known_values :
  arrange_particles 0 = 1 ∧ 
  arrange_particles 1 = 1 ∧
  arrange_particles 2 = 2 ∧
  arrange_particles 3 = 4 ∧
  arrange_particles 4 = 6 := sorry
-- </vc-theorems>