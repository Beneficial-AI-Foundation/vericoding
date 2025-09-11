-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ceil (x : Int) : Int := sorry

def cost (mins: Int) : Int := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem cost_minimum_30 (mins: Nat) : 
  cost mins ≥ 30 := sorry

theorem cost_base_rate (mins: Nat) (h: mins ≤ 65) : 
  cost mins = 30 := sorry

theorem cost_negative_zero (mins: Int) :
  mins < 0 → cost mins = cost 0 := sorry

theorem cost_stepwise_increase (mins: Nat) (h: 66 ≤ mins) :
  cost (mins - 1) ≤ cost mins ∧ cost mins - cost (mins - 1) ≤ 10 := sorry

/-
info: 30
-/
-- #guard_msgs in
-- #eval cost 45

/-
info: 30
-/
-- #guard_msgs in
-- #eval cost 63

/-
info: 40
-/
-- #guard_msgs in
-- #eval cost 84
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible