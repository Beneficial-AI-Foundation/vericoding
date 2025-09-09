-- <vc-helpers>
-- </vc-helpers>

def psion_power_points (level intelligence : Nat) : Nat :=
  sorry

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

/-
info: 0
-/
-- #guard_msgs in
-- #eval psion_power_points 1 0

/-
info: 0
-/
-- #guard_msgs in
-- #eval psion_power_points 1 10

/-
info: 2
-/
-- #guard_msgs in
-- #eval psion_power_points 1 11

/-
info: 4
-/
-- #guard_msgs in
-- #eval psion_power_points 1 20

/-
info: 448
-/
-- #guard_msgs in
-- #eval psion_power_points 21 30

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible