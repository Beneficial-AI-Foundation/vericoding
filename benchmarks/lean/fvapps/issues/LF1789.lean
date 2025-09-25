-- <vc-preamble>
def min_push_box (grid: Grid) : Int := sorry

def charEq (c1 c2 : Char) : Bool := c1.val = c2.val

def isValidCharProp (c: Char) : Prop := 
  c = '#' ∨ c = '.' ∨ c = 'S' ∨ c = 'B' ∨ c = 'T'
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isValidGrid (grid: Grid) : Prop := sorry

-- All grids must have exactly one player (S), one box (B) and one target (T)
-- </vc-definitions>

-- <vc-theorems>
theorem valid_grid_unique_elements (grid: Grid) (h: isValidGrid grid) :
  ∃ (s_pos b_pos t_pos : Nat × Nat),
    (grid.cells.get? s_pos.1).bind (·.get? s_pos.2) = some 'S' ∧ 
    (grid.cells.get? b_pos.1).bind (·.get? b_pos.2) = some 'B' ∧
    (grid.cells.get? t_pos.1).bind (·.get? t_pos.2) = some 'T' := sorry

-- A minimal valid grid should be solvable with one push

theorem minimal_valid_grid_solvable (grid: Grid) :
  isValidGrid grid →
  grid.cells = [['#','#','#'], ['#','S','#'], ['#','B','#'], ['#','T','#'], ['#','#','#']] →
  min_push_box grid = 1 := sorry

-- Some valid grids are unsolvable

theorem unsolvable_grid_exists (grid: Grid) :
  isValidGrid grid →
  grid.cells = [['#','#','#','#'], ['#','S','#','#'], ['#','B','T','#'], ['#','#','#','#']] →
  min_push_box grid = -1 := sorry

-- Empty grid is invalid and should result in error

theorem empty_grid_invalid :
  ¬ isValidGrid ⟨[]⟩ := sorry

-- Valid grid contains only allowed characters 

theorem valid_grid_chars (grid: Grid) (h: isValidGrid grid) :
  ∀ row ∈ grid.cells, ∀ c ∈ row, isValidCharProp c := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval min_push_box [["#", "#", "#", "#", "#", "#"], ["#", "T", "#", "#", "#", "#"], ["#", ".", ".", "B", ".", "#"], ["#", ".", "#", "#", ".", "#"], ["#", ".", ".", ".", "S", "#"], ["#", "#", "#", "#", "#", "#"]]

/-
info: -1
-/
-- #guard_msgs in
-- #eval min_push_box [["#", "#", "#", "#", "#", "#"], ["#", "T", "#", "#", "#", "#"], ["#", ".", ".", "B", ".", "#"], ["#", "#", "#", "#", ".", "#"], ["#", ".", ".", ".", "S", "#"], ["#", "#", "#", "#", "#", "#"]]

/-
info: -1
-/
-- #guard_msgs in
-- #eval min_push_box [["#", "#", "#", "#", "#", "#", "#"], ["#", "S", "#", ".", "B", "T", "#"], ["#", "#", "#", "#", "#", "#", "#"]]
-- </vc-theorems>