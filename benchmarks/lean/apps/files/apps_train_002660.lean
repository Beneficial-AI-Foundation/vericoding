-- <vc-helpers>
-- </vc-helpers>

def cockroach_speed (speed : Float) : Int :=
  sorry

theorem cockroach_speed_zero :
  cockroach_speed 0 = 0 :=
  sorry

/-
info: 30
-/
-- #guard_msgs in
-- #eval cockroach_speed 1.08

/-
info: 30
-/
-- #guard_msgs in
-- #eval cockroach_speed 1.09

/-
info: 0
-/
-- #guard_msgs in
-- #eval cockroach_speed 0

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible