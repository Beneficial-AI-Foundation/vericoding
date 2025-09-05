You are given several queries. Each query consists of three integers $p$, $q$ and $b$. You need to answer whether the result of $p/q$ in notation with base $b$ is a finite fraction.

A fraction in notation with base $b$ is finite if it contains finite number of numerals after the decimal point. It is also possible that a fraction has zero numerals after the decimal point.

-----Input-----

The first line contains a single integer $n$ ($1 \le n \le 10^5$) — the number of queries.

Next $n$ lines contain queries, one per line. Each line contains three integers $p$, $q$, and $b$ ($0 \le p \le 10^{18}$, $1 \le q \le 10^{18}$, $2 \le b \le 10^{18}$). All numbers are given in notation with base $10$.

-----Output-----

For each question, in a separate line, print Finite if the fraction is finite and Infinite otherwise.

-----Examples-----
Input
2
6 12 10
4 3 10

Output
Finite
Infinite

Input
4
1 1 2
9 36 2
4 12 3
3 5 4

Output
Finite
Finite
Finite
Infinite

-----Note-----

$\frac{6}{12} = \frac{1}{2} = 0,5_{10}$

$\frac{4}{3} = 1,(3)_{10}$

$\frac{9}{36} = \frac{1}{4} = 0,01_2$

$\frac{4}{12} = \frac{1}{3} = 0,1_3$

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: unguarded