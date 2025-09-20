-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Grid := List (List Nat)

def isPrintable (grid: Grid) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
def isValidGrid (grid: Grid) : Bool :=
  match grid with
  | [] => false
  | row::rows =>
    match row with
    | [] => false
    | _::_ =>
      let width := row.length
      rows.all (λ r => r.length = width)

theorem grid_validity {grid: Grid} (h: isValidGrid grid) :
  ∃ (row: List Nat) (rows: List (List Nat)), grid = row::rows :=
sorry

theorem printable_returns_bool (grid: Grid) :
  isPrintable grid = true ∨ isPrintable grid = false :=
sorry

theorem single_color_printable {grid: Grid} (h1: isValidGrid grid)
  (h2: ∀ (i j: Nat) (hi: i < grid.length) (hj: j < (grid.get ⟨i, hi⟩).length),
    (grid.get ⟨i, hi⟩).get ⟨j, hj⟩ = 1) :
  isPrintable grid = true :=
sorry

theorem symmetric_grid_printable_rotation {grid: Grid} {n: Nat}
  (h1: isValidGrid grid)
  (h2: grid.length = n)
  (h3: ∀ (i: Nat) (hi: i < grid.length),
    (grid.get ⟨i, hi⟩).length = n) :
  isPrintable grid = isPrintable (List.map List.reverse grid).reverse :=
sorry

theorem known_cases :
  (isPrintable [[1,1], [1,1]] = true) ∧
  (isPrintable [[1]] = true) ∧
  (isPrintable [[1,2], [2,1]] = false) :=
sorry
-- </vc-theorems>