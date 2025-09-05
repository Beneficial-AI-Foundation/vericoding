Almir had a small sequence $A_1, A_2, \ldots, A_N$. He decided to make $K$ copies of this sequence and concatenate them, forming a sequence $X_1, X_2, \ldots, X_{NK}$; for each valid $i$ and $j$ ($0 \le j < K$), $X_{j \cdot N + i} = A_i$.
For example, if $A = (1, 2, 3)$ and $K = 4$, the final sequence is $X = (1, 2, 3, 1, 2, 3, 1, 2, 3, 1, 2, 3)$.
A pair $(i, j)$, where $1 \le i < j \le N$, is an inversion if $X_i > X_j$. Find the number of inversions in the final sequence $X$.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains two space-separated integers $N$ and $K$.
- The second line contains $N$ space-separated integers $A_1, A_2, \ldots, A_N$.

-----Output-----
For each test case, print a single line containing one integer ― the number of inversions in the sequence $X$.

-----Constraints-----
- $1 \le T \le 1,000$
- $1 \le N \le 100$
- $1 \le K \le 10^6$
- $1 \le A_i \le 10^9$ for each valid $i$

-----Subtasks-----
Subtask #1 (100 points): original constraints

-----Example Input-----
2
3 3
2 1 3
4 100
99 2 1000 24

-----Example Output-----
12
30000

def count_inversions (arr : List Nat) (n : Nat) (m : Nat) : Nat := sorry

theorem count_inversions_non_negative (arr : List Nat) (n : Nat) (m : Nat) :
  count_inversions arr n m ≥ 0 := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded