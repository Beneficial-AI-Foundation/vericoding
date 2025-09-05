Chef received a new sequence $A_1, A_2, \ldots, A_N$. He does not like arbitrarily ordered sequences, so he wants to permute the elements of $A$ in such a way that it would satisfy the following condition: there is an integer $p$ ($1 \le p \le N$) such that the first $p$ elements of the new (permuted) sequence are strictly increasing and the last $N-p+1$ elements are strictly decreasing.
Help Chef and find a permutation of the given sequence which satisfies this condition or determine that no such permutation exists. If there are multiple solutions, you may find any one.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains a single integer $N$.
- The second line contains $N$ space-separated integers $A_1, A_2, \ldots, A_N$.

-----Output-----
For each test case:
- If there is no permutation of $A$ that satisfies the given condition, print a single line containing the string "NO" (without quotes).
- Otherwise, print two lines.
- The first of these lines should contain the string "YES" (without quotes).
- The second line should contain $N$ space-separated integers ― the elements of your permuted sequence.

-----Constraints-----
- $1 \le T \le 100$
- $1 \le N \le 10^5$
- $1 \le A_i \le 2 \cdot 10^5$ for each valid $i$
- the sum of $N$ over all test cases does not exceed $10^6$

-----Subtasks-----
Subtask #1 (50 points):
- $N \le 10^3$
- $A_i \le 2 \cdot 10^3$ for each valid $i$
- the sum of $N$ over all test cases does not exceed $10^4$
Subtask #2 (50 points): original constraints

-----Example Input-----
5
4
1 3 2 4
4
1 3 2 4
6
1 10 10 10 20 15
5
1 1 2 2 3
4
1 2 3 3

-----Example Output-----
YES
1 2 3 4
YES
4 3 2 1
NO
YES
1 2 3 2 1
NO

def List.countElem (x : α) (xs : List α) [BEq α] : Nat :=
xs.filter (· == x) |>.length

def List.uniqueElems (xs : List α) [BEq α] : List α :=
xs.eraseDups

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
