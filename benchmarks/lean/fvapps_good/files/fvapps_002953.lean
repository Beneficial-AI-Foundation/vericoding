-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def distance (p1 p2 : List Float) : Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem same_point_zero_distance (point : List Float) :
  distance point point = (if point.isEmpty then -1 else 0) :=
sorry

theorem different_length_arrays {p1 p2 : List Float} :
  p1.length ≠ p2.length → distance p1 p2 = -1 :=
sorry

theorem distance_is_symmetric {point : List Float} (h : point.length > 0) :
  let origin := List.replicate point.length 0
  distance origin point = distance point origin :=
sorry

theorem triangle_inequality {point : List Float} (h : point.length > 0) :
  let origin := List.replicate point.length 0
  let midpoint := point.map (fun x => x / 2)
  distance origin point ≤ distance origin midpoint + distance midpoint point :=
sorry
-- </vc-theorems>