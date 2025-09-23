-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculatePathDistance (p : Path) : Nat := sorry

theorem pathDistance_nonnegative (p : Path) :
  calculatePathDistance p ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem pathDistance_exceeds_y_diff (p : Path) (x : Nat) (yVals : List Nat) :
  yVals = (p.filter (fun pt => pt.1 == x)).map Prod.snd →
  yVals ≠ [] →
  calculatePathDistance p ≥ 0 := sorry

theorem pathDistance_exceeds_x_span (p : Path) :
  p.length > 1 →
  let xVals := p.map Prod.fst
  calculatePathDistance p ≥ 0 := sorry

theorem pathDistance_monotonic_right (p : Path) (newX newY : Nat) :
  p ≠ [] →
  newX > 0 →
  calculatePathDistance (p ++ [(newX, newY)]) ≥ calculatePathDistance p := sorry

theorem pathDistance_triangle_inequality (paths : List Path) :
  paths ≠ [] →
  let combinedPath := List.join paths
  ∀ path ∈ paths, calculatePathDistance combinedPath ≥ calculatePathDistance path := sorry
-- </vc-theorems>