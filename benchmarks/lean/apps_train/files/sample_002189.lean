We have a board with an H \times W grid.
Each square in the grid is painted in black or white. The square at the i-th row from the top and j-th column from the left is black if the j-th character in S_i is #, and white if that character is ..
Snuke can perform the following operation on the grid any number of times:
 - Select a row or column in the grid, and invert the color of all the squares in that row or column (that is, black squares become white and vice versa).
Then, Snuke draws a rectangle along grid lines. Here, all the squares contained in the rectangle must be painted in black.
Find the maximum possible area of Snuke's rectangle when the operation is performed optimally.

-----Constraints-----
 - 2 \leq H \leq 2000
 - 2 \leq W \leq 2000
 - |S_i| = W
 - S_i consists of # and ..

-----Input-----
Input is given from Standard Input in the following format:
H W
S_1
S_2
:
S_H

-----Output-----
Print the maximum possible area of Snuke's rectangle.

-----Sample Input-----
3 3
..#
##.
.#.

-----Sample Output-----
6

If the first row from the top and the third column from the left are inverted, a 2 \times 3 rectangle can be drawn, as shown below:

def toString (c : Char) : String := String.mk [c]

def mkString (n : Nat) (c : Char) : String := 
  String.mk (List.replicate n c)

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: unguarded
