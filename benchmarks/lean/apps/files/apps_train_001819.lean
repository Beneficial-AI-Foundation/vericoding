-- <vc-preamble>
def Grid := List (List Nat)

def shortest_bridge (grid: Grid) : Nat :=
  sorry

def is_valid_grid (grid: Grid) : Bool :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def has_two_islands (grid: Grid) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem shortest_bridge_non_negative 
  (grid: Grid) 
  (h1: is_valid_grid grid = true)
  (h2: has_two_islands grid = true) :
  shortest_bridge grid ≥ 0 :=
sorry

theorem shortest_bridge_less_than_dimensions
  (grid: Grid)
  (h1: is_valid_grid grid = true)
  (h2: has_two_islands grid = true) :
  shortest_bridge grid < grid.length * (grid.head!).length :=
sorry

theorem shortest_bridge_assumptions
  (grid: Grid)
  (h1: is_valid_grid grid = true)
  (h2: has_two_islands grid = true) :
  0 ≤ shortest_bridge grid ∧ shortest_bridge grid < grid.length * (grid.head!).length :=
sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval shortest_bridge [[0, 1], [1, 0]]

/-
info: 2
-/
-- #guard_msgs in
-- #eval shortest_bridge [[0, 1, 0], [0, 0, 0], [0, 0, 1]]

/-
info: 1
-/
-- #guard_msgs in
-- #eval shortest_bridge [[1, 1, 1, 1, 1], [1, 0, 0, 0, 1], [1, 0, 1, 0, 1], [1, 0, 0, 0, 1], [1, 1, 1, 1, 1]]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded