/-
Write a program to solve a Sudoku puzzle by filling the empty cells.

A sudoku solution must satisfy all of the following rules:

       Each of the digits 1-9 must occur exactly once in each row.
       Each of the digits 1-9 must occur exactly once in each column.
       Each of the the digits 1-9 must occur exactly once in each of the 9 3x3 sub-boxes of the grid.

Empty cells are indicated by the character '.'.

A sudoku puzzle...

...and its solution numbers marked in red.

Note:

       The given board contain only digits 1-9 and the character '.'.
       You may assume that the given Sudoku puzzle will have a single unique solution.
       The given board size is always 9x9.
-/

-- <vc-helpers>
-- </vc-helpers>

def is_valid_sudoku : Array (Array String) → Bool := 
  fun _ => sorry

theorem empty_board_valid (solver : SudokuSolver) (board : Array (Array String)) 
  (h : ∀ (i : Fin board.size) (j : Fin (board[i]!.size)), board[i]![j]! = ".") :
  let result := solver.solveSudoku board 
  -- Result is valid
  (is_valid_sudoku result ∧
  -- All cells contain digits 1-9  
  (∀ (i : Fin result.size) (j : Fin (result[i]!.size)), 
    result[i]![j]! ∈ ["1", "2", "3", "4", "5", "6", "7", "8", "9"]))
  := sorry

theorem partially_filled_board (solver : SudokuSolver)
  (board original : Array (Array String)) 
  (h₁ : board = original) :
  let result := solver.solveSudoku board
  -- Result is valid 
  (is_valid_sudoku result ∧
  -- All cells contain digits 1-9
  (∀ (i : Fin result.size) (j : Fin (result[i]!.size)),
    result[i]![j]! ∈ ["1", "2", "3", "4", "5", "6", "7", "8", "9"]) ∧ 
  -- Original numbers preserved
  (∀ (i : Fin original.size) (j : Fin (original[i]!.size)),
    original[i]![j]! ≠ "." → result[i]![j]! = original[i]![j]!))
  := sorry

-- Apps difficulty: interview
-- Assurance level: guarded