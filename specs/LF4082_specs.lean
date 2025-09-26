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
-- </vc-theorems>