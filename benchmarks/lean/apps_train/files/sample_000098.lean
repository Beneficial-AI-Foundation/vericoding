Lee was cleaning his house for the party when he found a messy string under the carpets. Now he'd like to make it clean accurately and in a stylish way...

The string $s$ he found is a binary string of length $n$ (i. e. string consists only of 0-s and 1-s).

In one move he can choose two consecutive characters $s_i$ and $s_{i+1}$, and if $s_i$ is 1 and $s_{i + 1}$ is 0, he can erase exactly one of them (he can choose which one to erase but he can't erase both characters simultaneously). The string shrinks after erasing.

Lee can make an arbitrary number of moves (possibly zero) and he'd like to make the string $s$ as clean as possible. He thinks for two different strings $x$ and $y$, the shorter string is cleaner, and if they are the same length, then the lexicographically smaller string is cleaner.

Now you should answer $t$ test cases: for the $i$-th test case, print the cleanest possible string that Lee can get by doing some number of moves.

Small reminder: if we have two strings $x$ and $y$ of the same length then $x$ is lexicographically smaller than $y$ if there is a position $i$ such that $x_1 = y_1$, $x_2 = y_2$,..., $x_{i - 1} = y_{i - 1}$ and $x_i < y_i$.

-----Input-----

The first line contains the integer $t$ ($1 \le t \le 10^4$) — the number of test cases. 

Next $2t$ lines contain test cases — one per two lines.

The first line of each test case contains the integer $n$ ($1 \le n \le 10^5$) — the length of the string $s$.

The second line contains the binary string $s$. The string $s$ is a string of length $n$ which consists only of zeroes and ones.

It's guaranteed that sum of $n$ over test cases doesn't exceed $10^5$.

-----Output-----

Print $t$ answers — one per test case.

The answer to the $i$-th test case is the cleanest string Lee can get after doing some number of moves (possibly zero).

-----Example-----
Input
5
10
0001111111
4
0101
8
11001101
10
1110000000
1
1

Output
0001111111
001
01
0
1

-----Note-----

In the first test case, Lee can't perform any moves.

In the second test case, Lee should erase $s_2$.

In the third test case, Lee can make moves, for example, in the following order: 11001101 $\rightarrow$ 1100101 $\rightarrow$ 110101 $\rightarrow$ 10101 $\rightarrow$ 1101 $\rightarrow$ 101 $\rightarrow$ 01.

def clean_binary_string (n : Nat) (s : String) : String := sorry

def string_of_zeros (n : Nat) : String := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
