-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isSolved (board : List (List Nat)) : Bool :=
  sorry

def isSequential (board : List (List Nat)) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem solved_board_generated {n : Nat} (h : n > 0) (h2 : n ≤ 5) :
  let board := List.map (fun i => List.map (fun j => n * i + j) (List.range n)) (List.range n)
  isSolved board = isSequential board :=
sorry

theorem arbitrary_boards_match_sequential (board : List (List Nat))
  (h : board.length > 0)
  (h2 : board.length ≤ 5)
  (h3 : ∀ row ∈ board, row.length = board.length) :
  isSolved board = isSequential board :=
sorry

theorem single_swap_breaks_solution
  {n : Nat} (h : n > 0) (h2 : n ≤ 5)
  (pos1 pos2 : Nat) (h3 : pos1 ≠ pos2) :
  let board := List.map (fun i => List.map (fun j => n * i + j) (List.range n)) (List.range n)
  let total_size := n * n
  let pos1' := pos1 % total_size
  let pos2' := pos2 % total_size
  let row1 := pos1' / n
  let col1 := pos1' % n
  let row2 := pos2' / n
  let col2 := pos2' % n
  let swapped_board := sorry
  ¬(isSolved swapped_board) :=
sorry
-- </vc-theorems>