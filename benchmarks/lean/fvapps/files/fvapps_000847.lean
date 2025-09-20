-- <vc-preamble>
def is_direction (c : Char) : Bool :=
  c = 'U' || c = 'D' || c = 'L' || c = 'R'
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_ant_grid (R C : Nat) (grid : List String) : Nat :=
  sorry

def make_empty_string (n : Nat) (c : Char) : String :=
  sorry

def count_directions (grid : List String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_ant_grid_output_props (R C : Nat) (grid : List String)
  (h : R > 0 ∧ C > 0) :
  let result := solve_ant_grid R C grid;
  result ≥ 0 :=
sorry

theorem empty_grid_zero_pairs (R C : Nat) (grid : List String)
  (h1 : R > 0 ∧ C > 0)
  (h2 : ∀ (row : String), row ∈ grid → ∀ (c : Char), c ∈ row.data → (c = '-' ∨ c = '#')) :
  solve_ant_grid R C grid = 0 :=
sorry

theorem single_ant_zero_pairs (R C : Nat) (grid : List String)
  (h1 : R > 0 ∧ C > 0)
  (h2 : count_directions grid ≤ 1) :
  solve_ant_grid R C grid = 0 :=
sorry

theorem all_empty_grid_zero (R C : Nat) (h : R > 0 ∧ C > 0) :
  let empty_row := make_empty_string C '-';
  let grid := List.replicate R empty_row;
  solve_ant_grid R C grid = 0 :=
sorry

theorem all_walls_grid_zero (R C : Nat) (h : R > 0 ∧ C > 0) :
  let wall_row := make_empty_string C '#';
  let grid := List.replicate R wall_row;
  solve_ant_grid R C grid = 0 :=
sorry

theorem single_ant_top_left_zero (R C : Nat) (ant : Char)
  (h1 : R > 0 ∧ C > 0)
  (h2 : is_direction ant) :
  let first_row := (String.push (make_empty_string (C-1) '-') ant);
  let empty_row := make_empty_string C '-';
  let rest_rows := List.replicate (R-1) empty_row;
  let grid := first_row :: rest_rows;
  solve_ant_grid R C grid = 0 :=
sorry
-- </vc-theorems>