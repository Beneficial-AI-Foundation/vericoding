-- <vc-preamble>
def isSolved (board : List (List Nat)) : Bool :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
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
  let swapped_board := sorry -- actual swapping implementation would go here
  ¬(isSolved swapped_board) :=
  sorry

/-
info: False
-/
-- #guard_msgs in
-- #eval is_solved [[1, 0], [3, 2]]

/-
info: False
-/
-- #guard_msgs in
-- #eval is_solved [[1, 0, 4], [3, 2, 7], [8, 5, 6]]

/-
info: True
-/
-- #guard_msgs in
-- #eval is_solved [[0, 1], [2, 3]]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded