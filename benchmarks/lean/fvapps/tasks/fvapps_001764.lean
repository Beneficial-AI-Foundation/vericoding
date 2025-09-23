-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def validTicTacToe (board : List String) : Bool :=
sorry

def hasWin (board : List String) (player : Char) : Bool :=
sorry

def countChar (board : List String) (c : Char) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem board_dimensions {board : List String} (h : validTicTacToe board) :
  board.length = 3 ∧
  (∀ row ∈ board, row.length = 3) ∧
  (∀ row ∈ board, ∀ c ∈ row.data, c = 'X' ∨ c = 'O' ∨ c = ' ') :=
sorry

theorem count_invariants {board : List String} (h : validTicTacToe board) :
  let x_count := countChar board 'X'
  let o_count := countChar board 'O'
  o_count ≤ x_count ∧ x_count - o_count ≤ 1 :=
sorry

theorem winner_invariants {board : List String} (h : validTicTacToe board) :
  let x_count := countChar board 'X'
  let o_count := countChar board 'O'
  let x_wins := hasWin board 'X'
  let o_wins := hasWin board 'O'
  ¬(x_wins ∧ o_wins) ∧
  ¬(x_wins ∧ x_count ≤ o_count) ∧
  ¬(o_wins ∧ x_count ≠ o_count) :=
sorry
-- </vc-theorems>