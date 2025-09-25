-- <vc-preamble>
def box (coords : List (Float × Float)) : Box :=
  sorry

def minList (l : List Float) : Float :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def maxList (l : List Float) : Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem box_bounds (coords : List (Float × Float)) (h : coords.length > 0) :
  let b := box coords
  let lats := coords.map (·.1)
  let longs := coords.map (·.2)
  b.nw.lat ≥ minList lats ∧ 
  b.nw.lat ≤ maxList lats ∧
  b.nw.long ≥ minList longs ∧
  b.nw.long ≤ maxList longs ∧
  b.se.lat ≥ minList lats ∧
  b.se.lat ≤ maxList lats ∧
  b.se.long ≥ minList longs ∧
  b.se.long ≤ maxList longs ∧
  b.nw.lat ≥ b.se.lat ∧
  b.se.long ≥ b.nw.long :=
  sorry

theorem single_point (coord : Float × Float) :
  let b := box [coord]
  b.nw.lat = coord.1 ∧
  b.nw.long = coord.2 ∧
  b.se.lat = coord.1 ∧
  b.se.long = coord.2 :=
  sorry
-- </vc-theorems>