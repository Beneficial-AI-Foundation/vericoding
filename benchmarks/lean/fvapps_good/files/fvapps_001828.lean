-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def largest1BorderedSquare (grid : List (List Nat)) : Nat := sorry

theorem all_zeros (n : Nat) (h : n ≥ 1) : 
  let grid := List.replicate n (List.replicate n 0)
  largest1BorderedSquare grid = 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem all_ones (n : Nat) (h : n ≥ 1) :
  let grid := List.replicate n (List.replicate n 1) 
  largest1BorderedSquare grid = n * n := sorry

theorem perfect_square_2x2 (grid : List (List Nat)) 
  (h1 : grid.length = 2)
  (h2 : ∀ row ∈ grid, row.length = 2)
  (h3 : ∀ row ∈ grid, ∀ x ∈ row, x = 0 ∨ x = 1) :
  let result := largest1BorderedSquare grid
  result * result = result := sorry

theorem bounds_3x3 (grid : List (List Nat))
  (h1 : grid.length = 3)
  (h2 : ∀ row ∈ grid, row.length = 3)
  (h3 : ∀ row ∈ grid, ∀ x ∈ row, x = 0 ∨ x = 1) :
  let result := largest1BorderedSquare grid
  let maxPossible := (min grid.length (grid.head?.getD []).length) ^ 2
  0 ≤ result ∧ result ≤ maxPossible := sorry
-- </vc-theorems>