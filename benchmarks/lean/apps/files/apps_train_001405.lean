/-
The XOR pair representation (XPR) of a positive integer $N$ is defined as a pair of integers $(A, B)$ such that:
- $1 \le A \le B \le N$
- $A \oplus B = N$
- if there is no way to choose $A$ and $B$ satisfying the above conditions, $A = B = -1$
- otherwise, the value of $A$ should be the smallest possible
These conditions uniquely define the XPR. Next, we define a function $F(N)$ = the value of $B$ in $XPR(N)$, and a function $G(L, R) = \sum\limits_{i=L}^R F(i)$.
You are given $L$ and $R$. Compute $G(L, R)$.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first and only line of each test case contains two space-separated integers $L$ and $R$.

-----Output-----
For each test case, print a single line containing one integer — the value of the function $G(L, R)$.

-----Constraints-----
- $1 \le T \le 10^5$
- $1 \le L \le R \le 10^9$

-----Example Input-----
5
1 10
3 6
4 10
10 17
100 159

-----Example Output-----
28
9
28
79
7485
-/

-- <vc-helpers>
-- </vc-helpers>

def solveXorPairs (l r : Nat) : Nat := sorry

theorem solveXorPairs_known_cases_1 : solveXorPairs 1 10 = 28 := sorry

theorem solveXorPairs_known_cases_2 : solveXorPairs 3 6 = 9 := sorry

theorem solveXorPairs_known_cases_3 : solveXorPairs 4 10 = 28 := sorry  

theorem solveXorPairs_known_cases_4 : solveXorPairs 10 17 = 79 := sorry

theorem solveXorPairs_known_cases_5 : solveXorPairs 100 159 = 7485 := sorry

-- Apps difficulty: interview
-- Assurance level: guarded