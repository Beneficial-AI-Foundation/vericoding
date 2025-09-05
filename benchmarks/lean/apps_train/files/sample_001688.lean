## A Knight's Tour

A knight's tour is a sequence of moves of a knight on a chessboard such that the knight visits every square only once.

https://en.wikipedia.org/wiki/Knight%27s_tour

Traditional chess boards are 8x8 grids, but for this kata we are interested in generating tours for any square board sizes.

You will be asked to find a knight's path for any NxN board from any start position.

I have provided a tool to visualize the output of your code at the following link: http://jsfiddle.net/7sbyya59/2/

EDIT: The expected output is a 2D array `(n x 2)` comprised of the `[x,y]` coordinates of the Knight's path taken in sequential order. (e.g. `[[2,3],[4,4],...,[x,y]]`)

All test cases will have a passing solution.

-dg

def knights_tour (start : Pos) (size : Nat) : List Pos :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded