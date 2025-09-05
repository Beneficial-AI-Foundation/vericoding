You are given two strings $S$ and $R$. Each of these strings has length $N$. We want to make $S$ equal to $R$ by performing the following operation some number of times (possibly zero):
- Choose two integers $a$ and $b$ such that $1 \le a \le b \le N$.
- For each $i$ such that $a \le i \le b$, replace the $i$-th character of $S$ by the $i$-th character of $R$.
Suppose that we make $S$ equal to $R$ by performing this operation $k$ times, in such a way that the total number of replaced characters (i.e. the sum of all $k$ values of $b-a+1$) is $l$. Then, the cost of this process is defined as $k \cdot l$.
Find the minimum cost with which we can make $S$ equal to $R$.

-----Input-----
- The first line of the input contains a single integer $T$ denoting the number of test cases. The description of $T$ test cases follows.
- The first line of each test case contains a single string $S$.
- The second line contains a single string $R$.

-----Output-----
For each test case, print a single line containing one integer ― the minimum cost.

-----Constraints-----
- $1 \le T \le 4,000$
- $1 \le N \le 10^6$
- $|S| = |R| = N$
- $S$ and $R$ contain only lowercase English letters
- the sum of $N$ over all test cases does not exceed $2 \cdot 10^6$

-----Example Input-----
1
adefb
bdefa

-----Example Output-----
4

-----Explanation-----
Example case 1: $S$ can be made equal to $R$ in two moves. First, we replace $S_1$ by $R_1$ and then replace $S_5$ by $R_5$. We have $k = l = 2$, so the cost is $2 \cdot 2 = 4$. If we wanted to perform only one operation, the cost would be $5$.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible