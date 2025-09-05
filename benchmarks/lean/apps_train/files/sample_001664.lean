Given two different positions on a chess board, find the least number of moves it would take a knight to get from one to the other.
The positions will be passed as two arguments in algebraic notation.
For example, `knight("a3", "b5")` should return 1.

The knight is not allowed to move off the board.
The board is 8x8.

For information on knight moves, see https://en.wikipedia.org/wiki/Knight_%28chess%29

For information on algebraic notation, see
https://en.wikipedia.org/wiki/Algebraic_notation_%28chess%29

(Warning: many of the tests were generated randomly. If any do not work, the test cases will return the input, output, and expected output; please post them.)

def abs (n : Nat) : Nat :=
  sorry

def isValidPos (pos : String) : Bool :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded