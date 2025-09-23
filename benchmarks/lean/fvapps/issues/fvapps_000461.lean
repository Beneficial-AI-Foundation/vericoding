-- <vc-preamble>
def isValidGrid (grid: Grid) : Bool :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def countIslands (grid: Grid) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_islands_basic_properties (grid: Grid) 
  (h: isValidGrid grid) : 
  let result := countIslands grid
  result ≥ 0 ∧ result ≤ grid.length * (grid.head!.length) := by
  sorry

theorem count_islands_preserves_grid (grid origGrid: Grid)
  (h: isValidGrid grid) (h2: grid = origGrid) :
  grid.length = origGrid.length ∧ 
  ∀ i < grid.length, grid[i]!.length = origGrid[i]!.length := by
  sorry

theorem zero_grid_has_no_islands (grid: Grid)
  (h: isValidGrid grid)
  (h2: ∀ i j, i < grid.length → j < (grid.head!.length) → 
        grid[i]![j]! = '0') :
  countIslands grid = 0 := by
  sorry

theorem no_adjacent_ones_after_counting (grid: Grid) (i j: Nat)
  (h: isValidGrid grid)
  (h2: i < grid.length) (h3: j < (grid.head!.length))
  (h4: grid[i]![j]! = '1') :
  let adjacent := [Pos.mk (i+1) j, Pos.mk (i-1) j, Pos.mk i (j+1), Pos.mk i (j-1)]
  ∀ p ∈ adjacent,
    p.row < grid.length → p.col < (grid.head!.length) →
    grid[p.row]![p.col]! ≠ '1' := by
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_islands [["1", "1", "1", "1", "0"], ["1", "1", "0", "1", "0"], ["1", "1", "0", "0", "0"], ["0", "0", "0", "0", "0"]]

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_islands [["1", "1", "0", "0", "0"], ["1", "1", "0", "0", "0"], ["0", "0", "1", "0", "0"], ["0", "0", "0", "1", "1"]]

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_islands [["0", "0", "0"], ["0", "0", "0"], ["0", "0", "0"]]
-- </vc-theorems>