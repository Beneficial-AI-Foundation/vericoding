Salmon is playing a game!
He is given two integers $N$ and $K$. His goal is to output $K$ pairs $(x_i,y_i)$. He creates a function $f$ such that $f(x_i) = y_i$ and $f$ is undefined for all other values of $x$. His pairs must then meet the following conditions:
- All $x_i$ are distinct.
- All $y_i$ are distinct.
- All $x_i, y_i$ are in the range $[0,2^N - 1]$ and are integers.
- $f(f(x_i))$ is defined for all $i$.
- Let $H(x)$ be the number of set bits in the binary representation of $x$. Then, $H(x_i) \neq H(f(f(x_i)))$ for all $i$.
Unfortunately, Salmon is unable to solve this. Help Salmon win the game!

If there are multiple correct solutions, you may output any one of them. It can be proven that a solution exists for all $N$ and $K$ that meet constraints.

-----Input-----
- The first line input contains a single integer $T$ denoting the number of testcases
- Each of the next $T$ lines contains two space-separated integers $N$ and $K$ respectively.

-----Output-----
- Output $K$ lines for each testcase.
- The $i$-th line of a testcase should contain two space-separated integers: $x_i$ and $y_i$, following the given constraints.

-----Constraints-----
- $1 \leq T \leq 2^{15}$
- $3 \leq N \leq 18$ 
- $3 \leq K \leq 2^N$ 
- The sum of $2^N$ over all testcases doesn't exceed $2^{18}$

-----Subtasks-----
- Subtask 1 [20 points]: $K \leq 8$
- Subtask 2 [40 points]: $K = 2^N$
- Subtask 3 [40 points]: No additional constraints.

-----Sample Input-----
2
3 7
4 6

-----Sample Output-----
5 3
1 7
0 4
2 5
3 1
4 2 
7 0
1 10
10 14
15 1
14 13
5 15
13 5

-----Explanation-----
In the answer to the first testcase, there are 7 pairs. $x_i$ and $y_i$ are all in the range $[0,2^3 - 1]$, which is the range $[0,7]$. All values of $x_i$ are distinct, and all values of $y_i$ are distinct. However, note that some integers appear in both lists. For example, 5 appears both as $x_1$ and as $y_4$. This is allowed. For all $x_i$, $f(f(x_i))$ is defined and $H(f(f(x_i))) \neq H(x_i)$. For example, $f(f(7)) = 4$. $H(7) = 3$, but $H(4) = 1$. Therefore, $H(f(f(7))) \neq H(7)$, as desired.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded