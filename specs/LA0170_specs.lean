-- <vc-preamble>
def ValidInput (stdin_input : String) : Prop :=
  stdin_input.length > 0

def ValidGrid (grid : Array (Array Int)) : Prop :=
  grid.size > 0 ∧ 
  (∀ row ∈ grid, row.size > 0) ∧
  (∀ i, i < grid.size → ∀ j, j < grid[i]!.size → grid[i]![j]! = 0 ∨ grid[i]![j]! = 1)

def power (base exp : Nat) : Nat := 
  base ^ exp

def count_in_row_helper (grid : Array (Array Int)) (row : Nat) (value : Int) (col : Nat) : Nat :=
  if col < grid[row]!.size then
    (if grid[row]![col]! = value then 1 else 0) + count_in_row_helper grid row value (col + 1)
  else 0
termination_by grid[row]!.size - col

def count_in_row (grid : Array (Array Int)) (row : Nat) (value : Int) : Nat :=
  if row < grid.size then count_in_row_helper grid row value 0 else 0

def count_col_helper (grid : Array (Array Int)) (col : Nat) (value : Int) (row : Nat) : Nat :=
  if row < grid.size then
    (if col < grid[row]!.size ∧ grid[row]![col]! = value then 1 else 0) + count_col_helper grid col value (row + 1)
  else 0
termination_by grid.size - row

def count_in_col (grid : Array (Array Int)) (col : Nat) (value : Int) : Nat :=
  if grid.size = 0 then 0 else count_col_helper grid col value 0

def row_contribution (grid : Array (Array Int)) (row : Nat) : Nat :=
  let cnt0 := count_in_row grid row 0
  let cnt1 := count_in_row grid row 1
  (if cnt0 > 1 then power 2 cnt0 - cnt0 - 1 else 0) +
  (if cnt1 > 1 then power 2 cnt1 - cnt1 - 1 else 0)

def sum_row_contributions_helper (grid : Array (Array Int)) (row : Nat) : Nat :=
  if row < grid.size then
    row_contribution grid row + sum_row_contributions_helper grid (row + 1)
  else 0
termination_by grid.size - row

def sum_row_contributions (grid : Array (Array Int)) : Nat :=
  sum_row_contributions_helper grid 0

def col_contribution (grid : Array (Array Int)) (col : Nat) : Nat :=
  let cnt0 := count_in_col grid col 0
  let cnt1 := count_in_col grid col 1
  (if cnt0 > 1 then power 2 cnt0 - cnt0 - 1 else 0) +
  (if cnt1 > 1 then power 2 cnt1 - cnt1 - 1 else 0)

def sum_col_contributions_helper (grid : Array (Array Int)) (col : Nat) (max_cols : Nat) : Nat :=
  if col < max_cols then
    col_contribution grid col + sum_col_contributions_helper grid (col + 1) max_cols
  else 0
termination_by max_cols - col

def sum_col_contributions (grid : Array (Array Int)) : Nat :=
  let max_cols := if grid.size > 0 then grid[0]!.size else 0
  sum_col_contributions_helper grid 0 max_cols

def count_valid_sets (grid : Array (Array Int)) : Nat :=
  let total_cells := grid.size * (if grid.size > 0 then grid[0]!.size else 0)
  total_cells + sum_row_contributions grid + sum_col_contributions grid

def int_to_string (n : Int) : String := toString n

@[reducible, simp]
def solve_precond (stdin_input : String) : Prop :=
  ValidInput stdin_input
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (stdin_input : String) (h_precond : solve_precond stdin_input) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
@[reducible, simp]
def solve_postcond (stdin_input : String) (result : String) (h_precond : solve_precond stdin_input) : Prop :=
  result.length > 0 ∧ 
  (result.length ≥ 1 → result.data[result.length - 1]! = '\n') ∧
  ∃ output_value : Int, output_value ≥ 0 ∧ result = int_to_string output_value ++ "\n"

theorem solve_spec_satisfied (stdin_input : String) (h_precond : solve_precond stdin_input) :
    solve_postcond stdin_input (solve stdin_input h_precond) h_precond := by
  sorry
-- </vc-theorems>