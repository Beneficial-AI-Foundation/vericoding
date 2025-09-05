You are given a rectangular parallelepiped with sides of positive integer lengths $A$, $B$ and $C$. 

Find the number of different groups of three integers ($a$, $b$, $c$) such that $1\leq a\leq b\leq c$ and parallelepiped $A\times B\times C$ can be paved with parallelepipeds $a\times b\times c$. Note, that all small parallelepipeds have to be rotated in the same direction.

For example, parallelepiped $1\times 5\times 6$ can be divided into parallelepipeds $1\times 3\times 5$, but can not be divided into parallelepipeds $1\times 2\times 3$.

-----Input-----

The first line contains a single integer $t$ ($1 \leq t \leq 10^5$) — the number of test cases.

Each of the next $t$ lines contains three integers $A$, $B$ and $C$ ($1 \leq A, B, C \leq 10^5$) — the sizes of the parallelepiped.

-----Output-----

For each test case, print the number of different groups of three points that satisfy all given conditions.

-----Example-----
Input
4
1 1 1
1 6 1
2 2 2
100 100 100

Output
1
4
4
165

-----Note-----

In the first test case, rectangular parallelepiped $(1, 1, 1)$ can be only divided into rectangular parallelepiped with sizes $(1, 1, 1)$.

In the second test case, rectangular parallelepiped $(1, 6, 1)$ can be divided into rectangular parallelepipeds with sizes $(1, 1, 1)$, $(1, 1, 2)$, $(1, 1, 3)$ and $(1, 1, 6)$.

In the third test case, rectangular parallelepiped $(2, 2, 2)$ can be divided into rectangular parallelepipeds with sizes $(1, 1, 1)$, $(1, 1, 2)$, $(1, 2, 2)$ and $(2, 2, 2)$.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: guarded_and_plausible
