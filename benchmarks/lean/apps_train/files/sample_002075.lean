There are some rabbits in Singapore Zoo. To feed them, Zookeeper bought $n$ carrots with lengths $a_1, a_2, a_3, \ldots, a_n$. However, rabbits are very fertile and multiply very quickly. Zookeeper now has $k$ rabbits and does not have enough carrots to feed all of them. To solve this problem, Zookeeper decided to cut the carrots into $k$ pieces. For some reason, all resulting carrot lengths must be positive integers.

Big carrots are very difficult for rabbits to handle and eat, so the time needed to eat a carrot of size $x$ is $x^2$.

Help Zookeeper split his carrots while minimizing the sum of time taken for rabbits to eat the carrots.

-----Input-----

The first line contains two integers $n$ and $k$ $(1 \leq n \leq k \leq 10^5)$: the initial number of carrots and the number of rabbits.

The next line contains $n$ integers $a_1, a_2, \ldots, a_n$ $(1 \leq a_i \leq 10^6)$: lengths of carrots.

It is guaranteed that the sum of $a_i$ is at least $k$.

-----Output-----

Output one integer: the minimum sum of time taken for rabbits to eat carrots.

-----Examples-----
Input
3 6
5 3 1

Output
15

Input
1 4
19

Output
91

-----Note-----

For the first test, the optimal sizes of carrots are $\{1,1,1,2,2,2\}$. The time taken is $1^2+1^2+1^2+2^2+2^2+2^2=15$

For the second test, the optimal sizes of carrots are $\{4,5,5,5\}$. The time taken is $4^2+5^2+5^2+5^2=91$.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: guarded
