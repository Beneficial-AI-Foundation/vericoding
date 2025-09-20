-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def pi : Float := 3.14159265359

def calculate_ice_cream_volumes (r1 h1 r2 h2 : Float) : Float × Float := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem volumes_are_positive (r1 h1 r2 h2 : Float) :
  let (vol1, vol2) := calculate_ice_cream_volumes r1 h1 r2 h2
  vol1 > 0 ∧ vol2 > 0 := sorry

theorem cylinder_volume_formula (r1 h1 r2 h2 : Float) :
  let (_, vol2) := calculate_ice_cream_volumes r1 h1 r2 h2 
  Float.abs (vol2 - pi * r2 * r2 * h2) < 0.000001 := sorry

theorem cone_hemisphere_volume_formula (r1 h1 r2 h2 : Float) :
  let (vol1, _) := calculate_ice_cream_volumes r1 h1 r2 h2
  let cone_vol := pi * r1 * r1 * h1 / 3 
  let hemisphere_vol := 2 * pi * r1 * r1 * r1 / 3
  Float.abs (vol1 - (cone_vol + hemisphere_vol)) < 0.000001 := sorry
-- </vc-theorems>