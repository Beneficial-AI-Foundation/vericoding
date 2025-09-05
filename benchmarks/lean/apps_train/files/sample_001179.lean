Chef played an interesting game yesterday. This game is played with two variables $X$ and $Y$; initially, $X = Y = 0$. Chef may make an arbitrary number of moves (including zero). In each move, he must perform the following process:
- Choose any positive integer $P$ such that $P \cdot P > Y$.
- Change $X$ to $P$.
- Add $P \cdot P$ to $Y$.
Unfortunately, Chef has a bad memory and he has forgotten the moves he made. He only remembers the value of $X$ after the game finished; let's denote it by $X_f$. Can you tell him the maximum possible number of moves he could have made in the game?

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first and only line of each test case contains a single integer $X_f$.

-----Output-----
For each test case, print a single line containing one integer — the maximum number of moves Chef could have made.

-----Constraints-----
- $1 \le T \le 10^5$
- $1 \le X_f \le 10^9$

-----Example Input-----
3
3
8
9

-----Example Output-----
3
5
6

-----Explanation-----
Example case 2: One possible sequence of values of $X$ is $0 \rightarrow 1 \rightarrow 2 \rightarrow 3 \rightarrow 5 \rightarrow 8$.

def calc_max_moves (n : Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible