-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def minimum_moves (grid : Array (Array Nat)) : Int := sorry

/- For any non-empty n×n grid with all zeros, there exists a valid path to reach bottom right -/
-- </vc-definitions>

-- <vc-theorems>
theorem min_moves_empty_grid_reaches {n : Nat} (h : n ≥ 3) :
  let grid := Array.mk (List.replicate n (Array.mk (List.replicate n (0:Nat))))
  minimum_moves grid > 0 := sorry
-- </vc-theorems>