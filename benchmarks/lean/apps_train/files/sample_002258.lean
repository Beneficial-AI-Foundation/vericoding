You are given two strings $s$ and $t$ both of length $n$ and both consisting of lowercase Latin letters.

In one move, you can choose any length $len$ from $1$ to $n$ and perform the following operation:   Choose any contiguous substring of the string $s$ of length $len$ and reverse it;  at the same time choose any contiguous substring of the string $t$ of length $len$ and reverse it as well. 

Note that during one move you reverse exactly one substring of the string $s$ and exactly one substring of the string $t$.

Also note that borders of substrings you reverse in $s$ and in $t$ can be different, the only restriction is that you reverse the substrings of equal length. For example, if $len=3$ and $n=5$, you can reverse $s[1 \dots 3]$ and $t[3 \dots 5]$, $s[2 \dots 4]$ and $t[2 \dots 4]$, but not $s[1 \dots 3]$ and $t[1 \dots 2]$.

Your task is to say if it is possible to make strings $s$ and $t$ equal after some (possibly, empty) sequence of moves.

You have to answer $q$ independent test cases.

-----Input-----

The first line of the input contains one integer $q$ ($1 \le q \le 10^4$) — the number of test cases. Then $q$ test cases follow.

The first line of the test case contains one integer $n$ ($1 \le n \le 2 \cdot 10^5$) — the length of $s$ and $t$.

The second line of the test case contains one string $s$ consisting of $n$ lowercase Latin letters.

The third line of the test case contains one string $t$ consisting of $n$ lowercase Latin letters.

It is guaranteed that the sum of $n$ over all test cases does not exceed $2 \cdot 10^5$ ($\sum n \le 2 \cdot 10^5$).

-----Output-----

For each test case, print the answer on it — "YES" (without quotes) if it is possible to make strings $s$ and $t$ equal after some (possibly, empty) sequence of moves and "NO" otherwise.

-----Example-----
Input
4
4
abcd
abdc
5
ababa
baaba
4
asdf
asdg
4
abcd
badc

Output
NO
YES
NO
YES

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded