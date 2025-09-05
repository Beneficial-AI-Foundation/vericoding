You are given three strings $a$, $b$ and $c$ of the same length $n$. The strings consist of lowercase English letters only. The $i$-th letter of $a$ is $a_i$, the $i$-th letter of $b$ is $b_i$, the $i$-th letter of $c$ is $c_i$.

For every $i$ ($1 \leq i \leq n$) you must swap (i.e. exchange) $c_i$ with either $a_i$ or $b_i$. So in total you'll perform exactly $n$ swap operations, each of them either $c_i \leftrightarrow a_i$ or $c_i \leftrightarrow b_i$ ($i$ iterates over all integers between $1$ and $n$, inclusive).

For example, if $a$ is "code", $b$ is "true", and $c$ is "help", you can make $c$ equal to "crue" taking the $1$-st and the $4$-th letters from $a$ and the others from $b$. In this way $a$ becomes "hodp" and $b$ becomes "tele".

Is it possible that after these swaps the string $a$ becomes exactly the same as the string $b$?

-----Input-----

The input consists of multiple test cases. The first line contains a single integer $t$ ($1 \leq t \leq 100$)  — the number of test cases. The description of the test cases follows.

The first line of each test case contains a string of lowercase English letters $a$.

The second line of each test case contains a string of lowercase English letters $b$.

The third line of each test case contains a string of lowercase English letters $c$.

It is guaranteed that in each test case these three strings are non-empty and have the same length, which is not exceeding $100$.

-----Output-----

Print $t$ lines with answers for all test cases. For each test case:

If it is possible to make string $a$ equal to string $b$ print "YES" (without quotes), otherwise print "NO" (without quotes).

You can print either lowercase or uppercase letters in the answers.

-----Example-----
Input
4
aaa
bbb
ccc
abc
bca
bca
aabb
bbaa
baba
imi
mii
iim

Output
NO
YES
YES
NO

-----Note-----

In the first test case, it is impossible to do the swaps so that string $a$ becomes exactly the same as string $b$.

In the second test case, you should swap $c_i$ with $a_i$ for all possible $i$. After the swaps $a$ becomes "bca", $b$ becomes "bca" and $c$ becomes "abc". Here the strings $a$ and $b$ are equal.

In the third test case, you should swap $c_1$ with $a_1$, $c_2$ with $b_2$, $c_3$ with $b_3$ and $c_4$ with $a_4$. Then string $a$ becomes "baba", string $b$ becomes "baba" and string $c$ becomes "abab". Here the strings $a$ and $b$ are equal.

In the fourth test case, it is impossible to do the swaps so that string $a$ becomes exactly the same as string $b$.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
