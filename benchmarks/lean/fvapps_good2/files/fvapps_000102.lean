-- <vc-preamble>
def countEmptyRows (grid : List (List Nat)) : Nat :=
  (grid.filter (fun row => row.all (fun x => x = 0))).length

def countEmptyCols (n m : Nat) (grid : List (List Nat)) : Nat :=
  let isEmptyCol (j : Nat) := (List.range n).all (fun i =>
    match grid.get? i with
    | none => true
    | some row => match row.get? j with
      | none => true
      | some x => x = 0)
  (List.range m).filter isEmptyCol |>.length
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_game (n m : Nat) (grid : List (List Nat)) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solve_game_returns_valid_winner (n m : Nat) (grid : List (List Nat))
  (h1 : n > 0) (h2 : m > 0) (h3 : grid.length = n)
  (h4 : ∀ row ∈ grid, row.length = m)
  (h5 : ∀ row ∈ grid, ∀ x ∈ row, x = 0 ∨ x = 1) :
  solve_game n m grid = "Ashish" ∨ solve_game n m grid = "Vivek" :=
sorry

theorem winner_depends_on_empty_lines (n m : Nat) (grid : List (List Nat))
  (h1 : n > 0) (h2 : m > 0) (h3 : grid.length = n)
  (h4 : ∀ row ∈ grid, row.length = m)
  (h5 : ∀ row ∈ grid, ∀ x ∈ row, x = 0 ∨ x = 1) :
  let empty_rows := countEmptyRows grid
  let empty_cols := countEmptyCols n m grid
  let min_empty := min empty_rows empty_cols
  solve_game n m grid = "Ashish" ↔ min_empty % 2 = 1 :=
sorry

theorem all_zeros_grid (n m : Nat) (h1 : n > 0) (h2 : m > 0) :
  let grid := List.replicate n (List.replicate m 0)
  solve_game n m grid = (if min n m % 2 = 1 then "Ashish" else "Vivek") :=
sorry

theorem no_empty_lines (n m : Nat) (h1 : n > 0) (h2 : m > 0) :
  let grid := List.replicate n (List.replicate m 1)
  solve_game n m grid = "Vivek" :=
sorry
-- </vc-theorems>