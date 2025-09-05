$n$ boys and $m$ girls came to the party. Each boy presented each girl some integer number of sweets (possibly zero). All boys are numbered with integers from $1$ to $n$ and all girls are numbered with integers from $1$ to $m$. For all $1 \leq i \leq n$ the minimal number of sweets, which $i$-th boy presented to some girl is equal to $b_i$ and for all $1 \leq j \leq m$ the maximal number of sweets, which $j$-th girl received from some boy is equal to $g_j$.

More formally, let $a_{i,j}$ be the number of sweets which the $i$-th boy give to the $j$-th girl. Then $b_i$ is equal exactly to the minimum among values $a_{i,1}, a_{i,2}, \ldots, a_{i,m}$ and $g_j$ is equal exactly to the maximum among values $b_{1,j}, b_{2,j}, \ldots, b_{n,j}$.

You are interested in the minimum total number of sweets that boys could present, so you need to minimize the sum of $a_{i,j}$ for all $(i,j)$ such that $1 \leq i \leq n$ and $1 \leq j \leq m$. You are given the numbers $b_1, \ldots, b_n$ and $g_1, \ldots, g_m$, determine this number. 

-----Input-----

The first line contains two integers $n$ and $m$, separated with space — the number of boys and girls, respectively ($2 \leq n, m \leq 100\,000$). The second line contains $n$ integers $b_1, \ldots, b_n$, separated by spaces — $b_i$ is equal to the minimal number of sweets, which $i$-th boy presented to some girl ($0 \leq b_i \leq 10^8$). The third line contains $m$ integers $g_1, \ldots, g_m$, separated by spaces — $g_j$ is equal to the maximal number of sweets, which $j$-th girl received from some boy ($0 \leq g_j \leq 10^8$).

-----Output-----

If the described situation is impossible, print $-1$. In another case, print the minimal total number of sweets, which boys could have presented and all conditions could have satisfied.

-----Examples-----
Input
3 2
1 2 1
3 4

Output
12
Input
2 2
0 1
1 0

Output
-1
Input
2 3
1 0
1 1 2

Output
4

-----Note-----

In the first test, the minimal total number of sweets, which boys could have presented is equal to $12$. This can be possible, for example, if the first boy presented $1$ and $4$ sweets, the second boy presented $3$ and $2$ sweets and the third boy presented $1$ and $1$ sweets for the first and the second girl, respectively. It's easy to see, that all conditions are satisfied and the total number of sweets is equal to $12$.

In the second test, the boys couldn't have presented sweets in such way, that all statements satisfied.

In the third test, the minimal total number of sweets, which boys could have presented is equal to $4$. This can be possible, for example, if the first boy presented $1$, $1$, $2$ sweets for the first, second, third girl, respectively and the second boy didn't present sweets for each girl. It's easy to see, that all conditions are satisfied and the total number of sweets is equal to $4$.

def List.maximum (l : List Nat) : Nat :=
  sorry

def List.minimum (l : List Nat) : Nat :=
  sorry

def List.sum (l : List Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: guarded
