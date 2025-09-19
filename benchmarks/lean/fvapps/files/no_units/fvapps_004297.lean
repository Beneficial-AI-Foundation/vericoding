-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def harmon_pointTrip (xA xB xC : Float) : Float := sorry

theorem harmon_point_identity (x : Float) : 
  ∀ ε, ε > 0 → harmon_pointTrip x (x + 2) (x + 2) - (x + 2) < ε := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem harmon_point_cross_ratio (xA xB xC : Float) :
  xA < xB → xB < xC →
  let xD := harmon_pointTrip xA xB xC
  ∀ ε, ε > 0 → ((xA - xC) * (xB - xD)) / ((xA - xD) * (xB - xC)) + 1 < ε := sorry
-- </vc-theorems>