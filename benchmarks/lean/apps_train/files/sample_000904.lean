Consider the following $4 \times 4$ pattern:
1  2  4  7
3  5  8 11
6  9 12 14
10 13 15 16

You are given an integer $N$. Print the $N \times N$ pattern of the same kind (containing integers $1$ through $N^2$).

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first and only line of each test case contains a single integer $N$.

-----Output-----
For each test case, print $N$ lines; each of them should contain $N$ space-separated integers.

-----Constraints-----
- $1 \le T \le 10$
- $1 \le N \le 100$

-----Subtasks-----
Subtask #1 (100 points): Original constraints

-----Example Input-----
1
4

-----Example Output-----
1 2 4 7
3 5 8 11
6 9 12 14
10 13 15 16

-----Explanation-----

def generate_pattern (n : Nat) : List (List Nat) :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded