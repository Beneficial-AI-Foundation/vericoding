You are given a positive integer $N$. Consider the sequence $S = (1, 2, \ldots, N)$. You should choose two elements of this sequence and swap them.
A swap is nice if there is an integer $M$ ($1 \le M < N$) such that the sum of the first $M$ elements of the resulting sequence is equal to the sum of its last $N-M$ elements. Find the number of nice swaps.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first and only line of each test case contains a single integer $N$.

-----Output-----
For each test case, print a single line containing one integer ― the number of nice swaps.

-----Constraints-----
- $1 \le T \le 10^6$
- $1 \le N \le 10^9$

-----Subtasks-----
Subtask #1 (10 points):
- $T \le 10$
- $N \le 10^3$
Subtask #2 (30 points):
- $T \le 10$
- $N \le 10^6$
Subtask #3 (60 points): original constraints

-----Example Input-----
5
1
2
3
4
7

-----Example Output-----
0
0
2
2
3

def canSplitEvenly (n : Nat) : Bool :=
  sorry

def countPossibleSwaps (n : Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
