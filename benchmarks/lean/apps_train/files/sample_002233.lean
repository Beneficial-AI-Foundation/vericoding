This is the easy version of the problem. The difference between the versions is the constraint on $n$ and the required number of operations. You can make hacks only if all versions of the problem are solved.

There are two binary strings $a$ and $b$ of length $n$ (a binary string is a string consisting of symbols $0$ and $1$). In an operation, you select a prefix of $a$, and simultaneously invert the bits in the prefix ($0$ changes to $1$ and $1$ changes to $0$) and reverse the order of the bits in the prefix.

For example, if $a=001011$ and you select the prefix of length $3$, it becomes $011011$. Then if you select the entire string, it becomes $001001$.

Your task is to transform the string $a$ into $b$ in at most $3n$ operations. It can be proved that it is always possible.

-----Input-----

The first line contains a single integer $t$ ($1\le t\le 1000$)  — the number of test cases. Next $3t$ lines contain descriptions of test cases.

The first line of each test case contains a single integer $n$ ($1\le n\le 1000$)  — the length of the binary strings.

The next two lines contain two binary strings $a$ and $b$ of length $n$.

It is guaranteed that the sum of $n$ across all test cases does not exceed $1000$.

-----Output-----

For each test case, output an integer $k$ ($0\le k\le 3n$), followed by $k$ integers $p_1,\ldots,p_k$ ($1\le p_i\le n$). Here $k$ is the number of operations you use and $p_i$ is the length of the prefix you flip in the $i$-th operation.

-----Example-----
Input
5
2
01
10
5
01011
11100
2
01
01
10
0110011011
1000110100
1
0
1

Output
3 1 2 1
6 5 2 5 3 1 2
0
9 4 1 2 10 4 1 2 1 5
1 1

-----Note-----

In the first test case, we have $01\to 11\to 00\to 10$.

In the second test case, we have $01011\to 00101\to 11101\to 01000\to 10100\to 00100\to 11100$.

In the third test case, the strings are already the same. Another solution is to flip the prefix of length $2$, which will leave $a$ unchanged.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: guarded
