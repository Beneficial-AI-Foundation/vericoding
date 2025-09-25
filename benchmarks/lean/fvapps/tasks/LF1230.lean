-- <vc-preamble>
def countStars (s : String) : Nat :=
  s.toList.filter (· = '*') |>.length

def listSum (l : List Nat) : Nat :=
  l.foldl (· + ·) 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Grid := List String

def isValidGrid (grid : Grid) : Bool :=
  sorry

def solveHauntedLand (grid : Grid) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_haunted_land_output_valid (grid : Grid)
  (h : isValidGrid grid = true) :
  solveHauntedLand grid ≥ 0 :=
sorry

theorem empty_grid_returns_zero (grid : Grid)
  (h1 : isValidGrid grid = true)
  (h2 : ∀ (row : String), List.contains grid row → ¬ row.contains '*') :
  solveHauntedLand grid = 0 :=
sorry

theorem single_house_returns_one (grid : Grid)
  (h1 : isValidGrid grid = true)
  (h2 : listSum (grid.map countStars) = 1) :
  solveHauntedLand grid = 1 :=
sorry

theorem result_bounded_by_dimensions (grid : Grid)
  (h : isValidGrid grid = true) :
  solveHauntedLand grid ≤ max grid.length (grid.head?.map String.length |>.getD 0) :=
sorry

theorem inhabited_houses_positive_time (grid : Grid)
  (h1 : isValidGrid grid = true)
  (h2 : ∃ (row : String), List.contains grid row ∧ row.contains '*') :
  solveHauntedLand grid ≥ 1 :=
sorry
-- </vc-theorems>