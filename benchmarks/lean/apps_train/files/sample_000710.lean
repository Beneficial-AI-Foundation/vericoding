You are given a matrix of integers $A$ with $N$ rows (numbered $1$ through $N$) and $M$ columns (numbered $1$ through $M$). Each element of this matrix is either $0$ or $1$.
A move consists of the following steps:
- Choose two different rows $r_1$ and $r_2$ or two different columns $c_1$ and $c_2$.
- Apply the bitwise OR operation with the second row/column on the first row/column. Formally, if you chose two rows, this means you should change $A_{r_1, k}$ to $A_{r_1, k} \lor A_{r_2, k}$ for each $1 \le k \le M$; if you chose two columns, then you should change $A_{k, c_1}$ to $A_{k, c_1} \lor A_{k, c_2}$ for each $1 \le k \le N$.
For each element of the matrix, compute the minimum number of moves required to make it equal to $1$ or determine that it is impossible. Note that these answers are independent, i.e. we are starting with the initial matrix for each of them.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains two space-separated integers $N$ and $M$.
- $N$ lines follow. For each $i$ ($1 \le i \le N$), the $i$-th of these lines contains $M$ integers $A_{i, 1}, A_{i, 2}, \dots, A_{i, M}$ NOT separated by spaces.

-----Output-----
For each test case, print $N$ lines. For each valid $i$, the $i$-th of these lines should contain $M$ space-separated integers; for each valid $j$, the $j$-th of these integers should be the minimum number of moves required to make $A_{i, j}$ equal to $1$, or $-1$ if it is impossible.

-----Constraints-----
- $1 \le T \le 100$
- $1 \le N, M \le 1,000$
- $A_{i, j} \in \{0, 1\}$ for each valid $i, j$
- the sum of $N \cdot M$ for all test cases does not exceed $1,000,000$

-----Example Input-----
1
3 3
010
000
001

-----Example Output-----
1 0 1
2 1 1
1 1 0

def Matrix := List (List Int)
def StrMatrix := List String

def solve_matrix_moves (n m : Nat) (matrix : StrMatrix) : Matrix :=
  sorry

def replicate_zeros (n : Nat) (m : Nat) : List String :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded