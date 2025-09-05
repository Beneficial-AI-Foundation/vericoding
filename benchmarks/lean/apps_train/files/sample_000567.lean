Let's call a sequence good if the sum of all its elements is $0$.
You have a sequence of integers $A_1, A_2, \ldots, A_N$. You may perform any number of operations on this sequence (including zero). In one operation, you should choose a valid index $i$ and decrease $A_i$ by $i$. Can you make the sequence good using these operations?

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains a single integer $N$.
- The second line contains $N$ space-separated integers $A_1, A_2, \ldots, A_N$.

-----Output-----
For each test case, print a single line containing the string "YES" if it is possible to make the given sequence good or "NO" if it is impossible.

-----Constraints-----
- $1 \le T \le 1,000$
- $1 \le N \le 10$
- $|A_i| \le 100$ for each valid $i$

-----Subtasks-----
Subtask #1 (10 points): $N = 1$
Subtask #2 (30 points): $N \le 2$
Subtask #3 (60 points): original constraints

-----Example Input-----
2
1
-1
2
1 2

-----Example Output-----
NO
YES

-----Explanation-----
Example case 2: We can perform two operations ― subtract $1$ from $A_1$ and $2$ from $A_2$.

def can_make_sequence_good (n : Nat) (sequence : List Int) : String := sorry

def sum_nonnegative (l : List Int) : Int := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
