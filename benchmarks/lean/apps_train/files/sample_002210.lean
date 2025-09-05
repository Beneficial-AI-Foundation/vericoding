Toad Pimple has an array of integers $a_1, a_2, \ldots, a_n$.

We say that $y$ is reachable from $x$ if $x<y$ and there exists an integer array $p$ such that $x = p_1 < p_2 < \ldots < p_k=y$, and $a_{p_i}\, \&\, a_{p_{i+1}} > 0$ for all integers $i$ such that $1 \leq i < k$.

Here $\&$ denotes the bitwise AND operation.

You are given $q$ pairs of indices, check reachability for each of them.

-----Input-----

The first line contains two integers $n$ and $q$ ($2 \leq n \leq 300\,000$, $1 \leq q \leq 300\,000$) — the number of integers in the array and the number of queries you need to answer.

The second line contains $n$ space-separated integers $a_1, a_2, \ldots, a_n$ ($0 \leq a_i \leq 300\,000$) — the given array.

The next $q$ lines contain two integers each. The $i$-th of them contains two space-separated integers $x_i$ and $y_i$ ($1 \leq x_i < y_i \leq n$). You need to check if $y_i$ is reachable from $x_i$. 

-----Output-----

Output $q$ lines. In the $i$-th of them print "Shi" if $y_i$ is reachable from $x_i$, otherwise, print "Fou".

-----Example-----
Input
5 3
1 3 0 2 1
1 3
2 4
1 4

Output
Fou
Shi
Shi

-----Note-----

In the first example, $a_3 = 0$. You can't reach it, because AND with it is always zero. $a_2\, \&\, a_4 > 0$, so $4$ is reachable from $2$, and to go from $1$ to $4$ you can use $p = [1, 2, 4]$.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: guarded
