-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def valid_board (board: List (List Char)) : Bool := sorry

def count_battleships (board: List (List Char)) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_battleships_empty {b: List (List Char)} (h1: b = []) : count_battleships b = 0 := sorry

theorem count_battleships_empty_row {b: List (List Char)} (h1: b = [[]]) : count_battleships b = 0 := sorry

theorem count_battleships_non_negative {b: List (List Char)} : count_battleships b ≥ 0 := sorry

theorem count_battleships_upper_bound {b: List (List Char)} :
  let x_count := fun (row : List Char) => (row.filter (fun c => c = 'X')).length
  let total_x := (List.map x_count b).foldr Nat.add 0
  count_battleships b ≤ total_x := sorry

theorem count_battleships_neighbors {b: List (List Char)} {i j: Nat} 
  (h1: i < b.length) 
  (h2: j < (b.get! i).length)
  (h3: (b.get! i).get! j = 'X') :
  let neighbors := [
    (i+1, j), (i-1, j), (i, j+1), (i, j-1)
  ].filter (fun (ni, nj) => 
    ni < b.length ∧ 
    nj < (b.get! ni).length ∧ 
    (b.get! ni).get! nj = 'X'
  )
  neighbors.length ≤ 2 := sorry

theorem count_battleships_single {b: List (List Char)} 
  (h1: b = [['X']]) : count_battleships b = 1 := sorry
-- </vc-theorems>