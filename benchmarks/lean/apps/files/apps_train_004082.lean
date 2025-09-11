-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def coordinates (angle : Float) (radius : Float) : Float × Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem coordinates_periodic (angle radius : Float) : 
  angle ≥ -1000 → angle ≤ 1000 → radius > 0 →
  coordinates angle radius = coordinates (angle + 360) radius := 
  sorry

theorem coordinates_mirror (angle radius : Float) :
  angle ≥ 0 → angle ≤ 360 → radius > 0 →
  let (x₁, y₁) := coordinates angle radius
  let (x₂, y₂) := coordinates (angle + 180) radius
  x₁ = -x₂ ∧ y₁ = -y₂ :=
  sorry

theorem coordinates_zero_angle (radius : Float) :
  radius > 0 →
  let (x, y) := coordinates 0 radius
  x = radius ∧ y = 0 :=
  sorry

/-
info: (0.0, 1.0)
-/
-- #guard_msgs in
-- #eval coordinates 90 1

/-
info: (0.7071067812, 0.7071067812)
-/
-- #guard_msgs in
-- #eval coordinates 45 1

/-
info: (9848.0775301221, 1736.4817766693)
-/
-- #guard_msgs in
-- #eval coordinates 1090 10000
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded