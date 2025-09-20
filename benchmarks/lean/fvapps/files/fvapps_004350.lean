-- <vc-preamble>
def Grid := List String

def GridList := List (List Char)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def how_many_bees (grid : Grid) : Nat := sorry
def how_many_bees_list (grid : GridList) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem how_many_bees_nonnegative (grid : Grid) :
  how_many_bees grid ≥ 0 := sorry

theorem grid_list_equiv (grid : Grid) :
  how_many_bees grid = how_many_bees_list (grid.map (·.data)) := sorry

theorem empty_grid :
  how_many_bees [] = 0 := sorry

theorem bees_upper_bound {grid : Grid} (h : grid ≠ []) :
  how_many_bees grid ≤ grid.length * grid.head!.length * 2 := sorry

theorem reverse_grid_equiv (grid : Grid) :
  let reversed := grid.map (fun s => ⟨s.data.reverse⟩)
  how_many_bees grid = how_many_bees reversed := sorry
-- </vc-theorems>