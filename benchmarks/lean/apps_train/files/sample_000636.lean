Chef had a sequence of positive integers with length $N + K$. He managed to calculate the arithmetic average of all elements of this sequence (let's denote it by $V$), but then, his little brother deleted $K$ elements from it. All deleted elements had the same value.
Chef still knows the remaining $N$ elements — a sequence $A_1, A_2, \ldots, A_N$. Help him with restoring the original sequence by finding the value of the deleted elements or deciding that there is some mistake and the described scenario is impossible.
Note that the if it is possible for the deleted elements to have the same value, then it can be proven that it is unique. Also note that this value must be a positive integer.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains three space-separated integers $N$, $K$ and $V$.
- The second line contains $N$ space-separated integers $A_1, A_2, \ldots, A_N$.

-----Output-----
For each test case, print a single line containing one integer — the value of the deleted elements, or $-1$ if there is a mistake.

-----Constraints-----
- $1 \le T \le 100$
- $1 \le N, K \le 100$
- $1 \le V \le 10^5$
- $1 \le A_i \le 10^5$ for each valid $i$

-----Subtasks-----
Subtask #1 (100 points): original constraints

-----Example Input-----
3
3 3 4
2 7 3
3 1 4
7 6 5
3 3 4
2 8 3

-----Example Output-----
4
-1
-1

def List.sum : List Nat → Nat 
  | [] => 0
  | x::xs => x + sum xs

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
