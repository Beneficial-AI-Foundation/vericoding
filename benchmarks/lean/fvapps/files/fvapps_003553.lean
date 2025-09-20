-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def chess_board (rows: Nat) (cols: Nat) : List (List Char) := sorry

theorem chess_board_dimensions (rows cols: Nat) 
    (h1: 0 < rows) (h2: 0 < cols) :
  let board := chess_board rows cols
  (board.length = rows) ∧ 
  (∀ row ∈ board, row.length = cols) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem chess_board_alternating (rows cols: Nat)
    (h1: 0 < rows) (h2: 0 < cols) :
  let board := chess_board rows cols
  (∀ r < rows, ∀ c < cols,
    -- Each cell is O or X
    ((board.get! r).get! c = 'O' ∨ (board.get! r).get! c = 'X') ∧
    -- Horizontally adjacent cells differ
    (c > 0 → (board.get! r).get! c ≠ (board.get! r).get! (c-1)) ∧
    -- Vertically adjacent cells differ 
    (r > 0 → (board.get! r).get! c ≠ (board.get! (r-1)).get! c)
  ) := sorry

theorem chess_board_square_diagonals (size: Nat) (h: 0 < size) :
  let board := chess_board size size
  ∀ i < size, (board.get! i).get! i = (board.get! 0).get! 0 := sorry
-- </vc-theorems>