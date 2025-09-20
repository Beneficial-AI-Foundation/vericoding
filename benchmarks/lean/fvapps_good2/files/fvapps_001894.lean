-- <vc-preamble>
def listSum (l: List Nat) : Nat :=
  match l with
  | [] => 0
  | x::xs => x + listSum xs
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Grid := List (List Nat)

def closed_island (grid : Grid) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem closed_island_non_negative (grid: Grid) :
  closed_island grid ≥ 0 :=
sorry

theorem closed_island_less_than_zeros (grid: Grid) :
  let countZeros (row: List Nat) := List.length (List.filter (λ x => x = 0) row)
  closed_island grid ≤ listSum (List.map countZeros grid) :=
sorry

theorem closed_island_small_grid (grid: Grid) (h1: grid.length < 3 ∨ (List.head! grid).length < 3) :
  closed_island grid = 0 :=
sorry

theorem closed_island_all_ones (grid: Grid)
  (h: ∀ row, List.elem row grid → ∀ x, List.elem x row → x = 1) :
  closed_island grid = 0 :=
sorry

theorem closed_island_all_zeros (grid: Grid)
  (h: ∀ row, List.elem row grid → ∀ x, List.elem x row → x = 0) :
  closed_island grid = 0 :=
sorry

theorem closed_island_simple_case_3x3 (grid: Grid)
  (h1: grid = [[1,1,1], [1,0,1], [1,1,1]]) :
  closed_island grid = 1 :=
sorry

theorem closed_island_simple_case_4x4 (grid: Grid)
  (h1: grid = [[1,1,1,1], [1,0,0,1], [1,0,0,1], [1,1,1,1]]) :
  closed_island grid = 1 :=
sorry

theorem closed_island_mutates_to_ones (grid: Grid)
  (h1: grid = [[1,1,1], [1,0,1], [1,1,1]]) :
  let _ := closed_island grid
  ∀ row, List.elem row grid → ∀ x, List.elem x row → x = 1 :=
sorry
-- </vc-theorems>