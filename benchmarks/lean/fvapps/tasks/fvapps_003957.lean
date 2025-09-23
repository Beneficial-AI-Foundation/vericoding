-- <vc-preamble>
def BLACK : Int := 1

def WHITE : Int := 0
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ant (grid : List (List Int)) (col : Int) (row : Int) (steps : Int)
  (direction : Int := 0) : List (List Int) :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ant_result_rectangular {grid : List (List Int)} {col row steps dir : Int}
  (h1: 0 ≤ col) (h2: 0 ≤ row) (h3: 0 ≤ steps) (h4: 0 ≤ dir) (h5: dir ≤ 3)
  (h6: grid.length > 0) (h7 : ∀ r ∈ grid, r.length = grid.head!.length) :
  let result := ant grid col row steps dir
  ∀ r ∈ result, r.length = result.head!.length :=
sorry

theorem ant_result_valid_colors {grid : List (List Int)} {col row steps dir : Int}
  (h1: 0 ≤ col) (h2: 0 ≤ row) (h3: 0 ≤ steps) (h4: 0 ≤ dir) (h5: dir ≤ 3) :
  let result := ant grid col row steps dir
  ∀ r ∈ result, ∀ cell ∈ r, cell = BLACK ∨ cell = WHITE :=
sorry

theorem ant_result_size {grid : List (List Int)} {col row steps dir : Int}
  (h1: 0 ≤ col) (h2: 0 ≤ row) (h3: 0 ≤ steps) (h4: 0 ≤ dir) (h5: dir ≤ 3) :
  let result := ant grid col row steps dir
  result.length ≥ grid.length ∧ result.head!.length ≥ grid.head!.length :=
sorry

theorem ant_preserves_input {grid : List (List Int)} {col row steps dir : Int}
  (h1: 0 ≤ col) (h2: 0 ≤ row) (h3: 0 ≤ steps) (h4: 0 ≤ dir) (h5: dir ≤ 3) :
  let result := ant grid col row steps dir
  grid = grid :=
sorry

theorem ant_zero_steps {grid : List (List Int)} {col row : Int}
  (h1: 0 ≤ col) (h2: 0 ≤ row) :
  ant grid col row 0 = grid :=
sorry
-- </vc-theorems>