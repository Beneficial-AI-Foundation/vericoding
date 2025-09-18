-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def psion_power_points (level intelligence : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem psion_power_points_non_negative (level intelligence : Nat) :
  psion_power_points level intelligence ≥ 0 :=
  sorry

theorem zero_level_gives_zero_points (intel : Nat) :
  psion_power_points 0 intel = 0 :=
  sorry

theorem low_intelligence_gives_zero (level intel : Nat) :
  intel ≤ 10 → psion_power_points level intel = 0 :=
  sorry

theorem higher_intelligence_more_points (level intel : Nat) :
  level > 0 → intel > 10 → 
  psion_power_points level (intel + 2) ≥ psion_power_points level intel :=
  sorry

theorem higher_level_more_points (level intel : Nat) :
  level < 20 →
  psion_power_points (level + 1) intel ≥ psion_power_points level intel :=
  sorry
-- </vc-theorems>