-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_parking (n k : Nat) (grid : List (List Nat)) : List Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem parking_properties (n k : Nat)
  (h1 : 1 ≤ n ∧ n ≤ 10)
  (h2 : 1 ≤ k ∧ k ≤ 20)
  (grid : List (List Nat))
  (h3 : grid.length = 4)
  (h4 : ∀ row ∈ grid, row.length = n) :
  let result := solve_parking n k grid;
  -- Result is a list
  result.length > 0
  -- First element is non-negative  
  ∧ result.head?.isSome
  ∧ (∀ h, result.head?.get h ≥ 0)
  -- If solution exists (head ≠ 1), then rest of list represents valid moves  
  ∧ (∀ h, result.head?.get h ≠ 1 → 
      -- Number of moves matches head
      result.tail.length = result.head?.get h
      -- Moves are valid format
      ∧ ∀ move ∈ result.tail,
          -- Car number in valid range
          0 ≤ move ∧ move ≤ k
          -- Row in valid range 
          ∧ 1 ≤ move ∧ move ≤ 4
          -- Column in valid range
          ∧ 1 ≤ move ∧ move ≤ n
      -- Solution has finite moves
      ∧ result.head?.get h ≤ 20000) :=
sorry

theorem empty_grid (n : Nat)
  (h1 : 1 ≤ n ∧ n ≤ 10)
  (grid : List (List Nat))
  (h2 : grid.length = 4)
  (h3 : ∀ row ∈ grid, row.length = n)
  (h4 : ∀ row ∈ grid, ∀ cell ∈ row, cell = 0) :
  let result := solve_parking n n grid;
  result.head? = some 0 :=
sorry
-- </vc-theorems>