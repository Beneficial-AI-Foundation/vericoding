-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solveTaxiTurns (coords : List (List Int)) : Option String := sorry

theorem result_is_valid (coords : List (List Int)) :
  match solveTaxiTurns coords with
  | none => True
  | some result => result = "yes yes" ∨ result = "no yes" ∨ result = "no no" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem two_points_yes_yes (p1 p2 : List Int) :
  solveTaxiTurns [p1, p2] = some "yes yes" := sorry

theorem yes_yes_implies_no_sharp_angles (coords : List (List Int)) (i : Nat) :
  solveTaxiTurns coords = some "yes yes" →
  i + 2 < coords.length →
  let p1 := coords[i]!
  let p2 := coords[i+1]!
  let p3 := coords[i+2]!
  let dx1 := p2[0]! - p1[0]!
  let dy1 := p2[1]! - p1[1]!
  let dx2 := p3[0]! - p2[0]!
  let dy2 := p3[1]! - p2[1]!
  let dot := dx1 * dx2 + dy1 * dy2
  let mag1 := Float.sqrt (Float.ofInt (dx1 * dx1 + dy1 * dy1))
  let mag2 := Float.sqrt (Float.ofInt (dx2 * dx2 + dy2 * dy2))
  let cosTheta := Float.ofInt dot / (mag1 * mag2)
  let angle := Float.acos (min 1 (max (-1) cosTheta))
  dx1 * dx1 + dy1 * dy1 > 0 ∧ dx2 * dx2 + dy2 * dy2 > 0 →
  angle ≤ 0.7853981633974483 + 0.00001 := sorry  -- π/4 as decimal

theorem same_points_is_none (x y : Int) :
  solveTaxiTurns [[x,y], [x,y]] = none := sorry

theorem coords_in_bounds (coords : List (List Int)) :
  solveTaxiTurns coords ≠ none →
  ∀ point ∈ coords, ∀ coord ∈ point, 0 ≤ coord ∧ coord ≤ 50 := sorry
-- </vc-theorems>