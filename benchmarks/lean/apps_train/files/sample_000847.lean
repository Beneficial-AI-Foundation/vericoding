You are given a grid with $R$ rows (numbered $1$ through $R$) and $C$ columns (numbered $1$ through $C$). Initially, each cell of this grid is either empty, contains an ant or an anteater. Each ant is moving in a fixed direction: up, down, left or right. The anteaters do not move.
The movement of ants happens in discrete steps. For example, when an ant is in the cell in the $i$-th row and $j$-th column at some point in time (in some step) and it is moving down, then in the next step, it enters the cell in the $(i+1)$-th row and $j$-th column. Two ants meet each other when they enter the same cell at the same point in time (in the same step). When ants meet, they do not interact in any way and keep moving in their fixed directions.
If an ant reaches an anteater, that anteater eats the ant, so the ant completely disappears. If an ant attempts to leave the grid, it also disappears. When two ants enter a cell containing an anteater at the same time, they are eaten before they could meet.
Calculate the total number of pairs of ants that meet each other.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains two space-separated integers $R$ and $C$.
- Each of the following $R$ lines contains a single string with length $C$. For each valid $i, j$, the $j$-th character in the $i$-th string is:
- '#' if the cell in the $i$-th row and $j$-th column of the grid contains an anteater
- 'U', 'D', 'L' or 'R' if this cell contains an ant moving up, down, left or right respectively
- '-' if this cell is empty

-----Output-----
For each test case, print a single line containing one integer — the number of pairs of ants that meet.

-----Constraints-----
- $1 \le T \le 10$
- $1 \le R, C \le 50$
- each string contains only characters 'U', 'D', 'L', 'R', '#' and '-'

-----Example Input-----
10
3 3
R--
---
--U
1 4
R--R
2 2
--
--
1 4
R--L
1 4
-R-L
1 4
-R#L
3 3
R-D
-#-
R-U
3 3
R-D
---
R#U
3 3
-D-
R-L
-U-
1 7
RLLLLLL

-----Example Output-----
1
0
0
0
1
0
3
2
6
3

def solve_ant_grid (R C : Nat) (grid : List String) : Nat :=
  sorry

def is_direction (c : Char) : Bool :=
  c = 'U' || c = 'D' || c = 'L' || c = 'R'

def make_empty_string (n : Nat) (c : Char) : String :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
