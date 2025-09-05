Ayoub thinks that he is a very smart person, so he created a function $f(s)$, where $s$ is a binary string (a string which contains only symbols "0" and "1"). The function $f(s)$ is equal to the number of substrings in the string $s$ that contains at least one symbol, that is equal to "1".

More formally, $f(s)$ is equal to the number of pairs of integers $(l, r)$, such that $1 \leq l \leq r \leq |s|$ (where $|s|$ is equal to the length of string $s$), such that at least one of the symbols $s_l, s_{l+1}, \ldots, s_r$ is equal to "1". 

For example, if $s = $"01010" then $f(s) = 12$, because there are $12$ such pairs $(l, r)$: $(1, 2), (1, 3), (1, 4), (1, 5), (2, 2), (2, 3), (2, 4), (2, 5), (3, 4), (3, 5), (4, 4), (4, 5)$.

Ayoub also thinks that he is smarter than Mahmoud so he gave him two integers $n$ and $m$ and asked him this problem. For all binary strings $s$ of length $n$ which contains exactly $m$ symbols equal to "1", find the maximum value of $f(s)$.

Mahmoud couldn't solve the problem so he asked you for help. Can you help him? 

-----Input-----

The input consists of multiple test cases. The first line contains a single integer $t$ ($1 \leq t \leq 10^5$)  — the number of test cases. The description of the test cases follows.

The only line for each test case contains two integers $n$, $m$ ($1 \leq n \leq 10^{9}$, $0 \leq m \leq n$) — the length of the string and the number of symbols equal to "1" in it.

-----Output-----

For every test case print one integer number — the maximum value of $f(s)$ over all strings $s$ of length $n$, which has exactly $m$ symbols, equal to "1".

-----Example-----
Input
5
3 1
3 2
3 3
4 0
5 2

Output
4
5
6
0
12

-----Note-----

In the first test case, there exists only $3$ strings of length $3$, which has exactly $1$ symbol, equal to "1". These strings are: $s_1 = $"100", $s_2 = $"010", $s_3 = $"001". The values of $f$ for them are: $f(s_1) = 3, f(s_2) = 4, f(s_3) = 3$, so the maximum value is $4$ and the answer is $4$.

In the second test case, the string $s$ with the maximum value is "101".

In the third test case, the string $s$ with the maximum value is "111".

In the fourth test case, the only string $s$ of length $4$, which has exactly $0$ symbols, equal to "1" is "0000" and the value of $f$ for that string is $0$, so the answer is $0$.

In the fifth test case, the string $s$ with the maximum value is "01010" and it is described as an example in the problem statement.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded