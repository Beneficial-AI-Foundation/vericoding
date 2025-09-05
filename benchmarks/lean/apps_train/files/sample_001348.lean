Recently, Chef found a new formula for computing powers of a sequence:
- You are given two sequences $A_1, A_2, \ldots, A_N$ and $(l_1, r_1), (l_2, r_2), \ldots, (l_N, r_N)$.
- The $1$-st power of the sequence $A$ is $A^1 = A$.
- For each $k > 1$, the $k$-th power of the sequence $A$ (denoted by $A^k$) is a sequence with length $N$ such that for each valid $i$, the $i$-th element of this sequence is (Ak)i=(Ak−1)li⊕(Ak−1)li+1⊕…⊕(Ak−1)ri−1⊕(Ak−1)ri.(Ak)i=(Ak−1)li⊕(Ak−1)li+1⊕…⊕(Ak−1)ri−1⊕(Ak−1)ri.(A^k)_i = (A^{k-1})_{l_i} \oplus (A^{k-1})_{l_i+1} \oplus \ldots \oplus (A^{k-1})_{r_i-1} \oplus (A^{k-1})_{r_i} \,.
After discovering this new formula, Chef tried to find $A^K$, but he felt that it is very time consuming. Therefore, Chef wants you to do it. Can you find the $K$-th power of $A$ for Chef?

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains two space-separated integers $N$ and $K$.
- The second line contains $N$ space-separated integers $A_1, A_2, \ldots, A_N$.
- $N$ lines follow. For each valid $i$, the $i$-th of these lines contains two space-separated integers $l_i$ and $r_i$.

-----Output-----
For each test case, print a single line containing $N$ space-separated integers $(A^K)_1, (A^K)_2, \ldots, (A^K)_N$.

-----Constraints-----
- $1 \le T \le 3$
- $1 \le N \le 500$
- $1 \le K \le 5 \cdot 10^7$
- $1 \le A_i \le 10^{18}$ for each valid $i$
- $1 \le l_i \le r_i \le N$ for each valid $i$

-----Subtasks-----
Subtask #1 (50 points):
- $T = 1$
- $N \le 100$
Subtask #2 (50 points): original constraints

-----Sample Input-----
1
3 2
1 2 3
1 2
2 3
1 3

-----Example Ouput-----
3 1 0

-----Explanation-----
Example case 1:
- $(A^2)_1 = A_1 \oplus A_2 = 1 \oplus 2 = 3$
- $(A^2)_2 = A_2 \oplus A_3 = 2 \oplus 3 = 1$
- $(A^2)_3 = A_1 \oplus A_2 \oplus A_3 =1 \oplus 2 \oplus 3 = 0$

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
