Being tired of participating in too many Codeforces rounds, Gildong decided to take some rest in a park. He sat down on a bench, and soon he found two rabbits hopping around. One of the rabbits was taller than the other.

He noticed that the two rabbits were hopping towards each other. The positions of the two rabbits can be represented as integer coordinates on a horizontal line. The taller rabbit is currently on position $x$, and the shorter rabbit is currently on position $y$ ($x \lt y$). Every second, each rabbit hops to another position. The taller rabbit hops to the positive direction by $a$, and the shorter rabbit hops to the negative direction by $b$.

 [Image] 

For example, let's say $x=0$, $y=10$, $a=2$, and $b=3$. At the $1$-st second, each rabbit will be at position $2$ and $7$. At the $2$-nd second, both rabbits will be at position $4$.

Gildong is now wondering: Will the two rabbits be at the same position at the same moment? If so, how long will it take? Let's find a moment in time (in seconds) after which the rabbits will be at the same point.

-----Input-----

Each test contains one or more test cases. The first line contains the number of test cases $t$ ($1 \le t \le 1000$).

Each test case contains exactly one line. The line consists of four integers $x$, $y$, $a$, $b$ ($0 \le x \lt y \le 10^9$, $1 \le a,b \le 10^9$) — the current position of the taller rabbit, the current position of the shorter rabbit, the hopping distance of the taller rabbit, and the hopping distance of the shorter rabbit, respectively.

-----Output-----

For each test case, print the single integer: number of seconds the two rabbits will take to be at the same position.

If the two rabbits will never be at the same position simultaneously, print $-1$.

-----Example-----
Input
5
0 10 2 3
0 10 3 3
900000000 1000000000 1 9999999
1 2 1 1
1 3 1 1

Output
2
-1
10
-1
1

-----Note-----

The first case is explained in the description.

In the second case, each rabbit will be at position $3$ and $7$ respectively at the $1$-st second. But in the $2$-nd second they will be at $6$ and $4$ respectively, and we can see that they will never be at the same position since the distance between the two rabbits will only increase afterward.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible
