Chef has a sequence $A_1, A_2, \ldots, A_N$. This sequence has exactly $2^N$ subsequences. Chef considers a subsequence of $A$ interesting if its size is exactly $K$ and the sum of all its elements is minimum possible, i.e. there is no subsequence with size $K$ which has a smaller sum.
Help Chef find the number of interesting subsequences of the sequence $A$.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains two space-separated integers $N$ and $K$.
- The second line contains $N$ space-separated integers $A_1, A_2, \ldots, A_N$.

-----Output-----
For each test case, print a single line containing one integer ― the number of interesting subsequences.

-----Constraints-----
- $1 \le T \le 10$
- $1 \le K \le N \le 50$
- $1 \le A_i \le 100$ for each valid $i$

-----Subtasks-----
Subtask #1 (30 points): $1 \le N \le 20$
Subtask #2 (70 points): original constraints

-----Example Input-----
1
4 2
1 2 3 4

-----Example Output-----
1

-----Explanation-----
Example case 1: There are six subsequences with length $2$: $(1, 2)$, $(1, 3)$, $(1, 4)$, $(2, 3)$, $(2, 4)$ and $(3, 4)$. The minimum sum is $3$ and the only subsequence with this sum is $(1, 2)$.

def count_interesting_subsequences (n k : Nat) (a : List Nat) : Nat :=
  sorry

def isSorted (l : List Nat) : Bool :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded