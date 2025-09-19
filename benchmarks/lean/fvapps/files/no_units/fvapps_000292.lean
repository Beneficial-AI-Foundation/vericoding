-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Grid := List (List Nat)

def min_cost_to_valid_path (grid: Grid) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_constraints (grid: Grid) :
  let result := min_cost_to_valid_path grid
  result = -1 ∨ result ≥ 0 :=
sorry

theorem single_cell_case (grid: Grid) :
  grid.length = 1 → 
  (grid.head?.map List.head?).isSome →
  min_cost_to_valid_path grid = 0 :=
sorry

theorem size_bound (grid: Grid) (h: grid.length ≥ 2) :
  let result := min_cost_to_valid_path grid
  let n := grid.length
  result = -1 ∨ result < n * n :=
sorry
-- </vc-theorems>