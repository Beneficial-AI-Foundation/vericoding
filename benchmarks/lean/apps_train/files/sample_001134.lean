Guddu was participating in a programming contest. He only had one problem left when his mother called him for dinner. Guddu is well aware how angry his mother could get if he was late for dinner and he did not want to sleep on an empty stomach, so he had to leave that last problem to you. Can you solve it on his behalf?
For a given sequence of positive integers $A_1, A_2, \ldots, A_N$, you are supposed to find the number of triples $(i, j, k)$ such that $1 \le i < j \le k \le N$ and
Ai⊕Ai+1⊕…⊕Aj−1=Aj⊕Aj+1⊕…⊕Ak,Ai⊕Ai+1⊕…⊕Aj−1=Aj⊕Aj+1⊕…⊕Ak,A_i \oplus A_{i+1} \oplus \ldots \oplus A_{j-1} = A_j \oplus A_{j+1} \oplus \ldots \oplus A_k \,,
where $\oplus$ denotes bitwise XOR.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains a single integer $N$.
- The second line contains $N$ space-separated integers $A_1, A_2, \ldots, A_N$.

-----Output-----
For each test case, print a single line containing one integer ― the number of triples.

-----Constraints-----
- $1 \le T \le 10$
- $2 \le N \le 10^5$
- $1 \le A_i \le 10^6$ for each valid $i$

-----Subtasks-----
Subtask #1 (20 points):
- $1 \le T \le 5$
- $1 \le N \le 100$
Subtask #2 (30 points):
- $1 \le T \le 5$
- $1 \le N \le 1,000$
Subtask #3 (50 points): original constraints

-----Example Input-----
1
3
5 2 7

-----Example Output-----
2

-----Explanation-----
Example case 1: The triples are $(1, 3, 3)$, since $5 \oplus 2 = 7$, and $(1, 2, 3)$, since $5 = 2 \oplus 7$.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible