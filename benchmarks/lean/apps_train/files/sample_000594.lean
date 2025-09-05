"What do you know about happiness?" — Yoda 
Chef is happy only if three conditions hold:
- Chef finished cooking a delicious meal
- Chef got AC for a programming problem with an almost correct code
- Chef got a new problem with a sequence of integers
Today, all three conditions are satisfied. Chef would like you to feel his happiness and provide him with a solution for this new problem with a sequence of integers. The problem is as follows.
You are given a sequence $A_1, A_2, \dots, A_N$. You need to determine if it is possible to choose two indices $i$ and $j$ such that $A_i \neq A_j$, but $A_{A_i}$ = $A_{A_j}$. (If it was possible, Chef would be truly happy.)

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains a single integer $N$.
- The second line contains $N$ space-separated integers $A_1, A_2, \ldots, A_N$.

-----Output-----
For each test case, print a single line containing the string "Truly Happy" if it is possible to choose required indices or "Poor Chef" otherwise.

-----Constraints-----
- $1 \le T \le 1,000$
- $1 \le N \le 10^5$
- $1 \le A_i \le N$ for each valid $i$
- the sum of $N$ over all test cases does not exceed $2 \cdot 10^5$

-----Subtasks-----
Subtask #1 (27 points): $1 \le N \le 1,000$
Subtask #2 (73 points): original constraints

-----Example Input-----
4
4
1 1 2 3
4
2 1 3 3
5
5 4 4 3 1
5
3 2 1 1 4

-----Example Output-----
Truly Happy
Poor Chef
Poor Chef
Truly Happy

-----Explanation-----
Example case 1: Chef is truly happy because $A_{A_3} = A_{A_1}$ and $A_3 \neq A_1$.
Example case 2: There is no pair of indices which would make Chef truly happy. For instance, $A_{A_3} = A_{A_4}$, but $A_3 = A_4$,

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded