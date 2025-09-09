/-
A Tic-Tac-Toe board is given as a string array board. Return True if and only if it is possible to reach this board position during the course of a valid tic-tac-toe game.

The board is a 3 x 3 array, and consists of characters " ", "X", and "O".  The " " character represents an empty square.

Here are the rules of Tic-Tac-Toe:

       Players take turns placing characters into empty squares (" ").
       The first player always places "X" characters, while the second player always places "O" characters.
       "X" and "O" characters are always placed into empty squares, never filled ones.
       The game ends when there are 3 of the same (non-empty) character filling any row, column, or diagonal.
       The game also ends if all squares are non-empty.
       No more moves can be played if the game is over.

Example 1:
Input: board = ["O  ", "   ", "   "]
Output: false
Explanation: The first player always plays "X".

Example 2:
Input: board = ["XOX", " X ", "   "]
Output: false
Explanation: Players take turns making moves.

Example 3:
Input: board = ["XXX", "   ", "OOO"]
Output: false

Example 4:
Input: board = ["XOX", "O O", "XOX"]
Output: true

Note:

       board is a length-3 array of strings, where each string board[i] has length 3.
       Each board[i][j] is a character in the set {" ", "X", "O"}.
-/

def validTicTacToe (board : List String) : Bool := sorry

def hasWin (board : List String) (player : Char) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

def countChar (board : List String) (c : Char) : Nat := sorry

theorem board_dimensions {board : List String} (h : validTicTacToe board) :
  board.length = 3 ∧ 
  (∀ row ∈ board, row.length = 3) ∧
  (∀ row ∈ board, ∀ c ∈ row.data, c = 'X' ∨ c = 'O' ∨ c = ' ') := sorry

theorem count_invariants {board : List String} (h : validTicTacToe board) :
  let x_count := countChar board 'X'
  let o_count := countChar board 'O'
  o_count ≤ x_count ∧ x_count - o_count ≤ 1 := sorry

theorem winner_invariants {board : List String} (h : validTicTacToe board) :
  let x_count := countChar board 'X'
  let o_count := countChar board 'O'
  let x_wins := hasWin board 'X'
  let o_wins := hasWin board 'O'
  ¬(x_wins ∧ o_wins) ∧
  ¬(x_wins ∧ x_count ≤ o_count) ∧ 
  ¬(o_wins ∧ x_count ≠ o_count) := sorry

/-
info: False
-/
-- #guard_msgs in
-- #eval validTicTacToe ["O  ", "   ", "   "]

/-
info: False
-/
-- #guard_msgs in
-- #eval validTicTacToe ["XOX", " X ", "   "]

/-
info: True
-/
-- #guard_msgs in
-- #eval validTicTacToe ["XOX", "O O", "XOX"]

-- Apps difficulty: interview
-- Assurance level: unguarded