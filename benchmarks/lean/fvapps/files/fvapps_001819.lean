-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Grid := List (List Nat)

def shortest_bridge (grid: Grid) : Nat :=
  sorry

def is_valid_grid (grid: Grid) : Bool :=
  sorry

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
-- </vc-theorems>