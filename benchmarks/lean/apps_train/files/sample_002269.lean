You are given a garland consisting of $n$ lamps. States of the lamps are represented by the string $s$ of length $n$. The $i$-th character of the string $s_i$ equals '0' if the $i$-th lamp is turned off or '1' if the $i$-th lamp is turned on. You are also given a positive integer $k$.

In one move, you can choose one lamp and change its state (i.e. turn it on if it is turned off and vice versa).

The garland is called $k$-periodic if the distance between each pair of adjacent turned on lamps is exactly $k$. Consider the case $k=3$. Then garlands "00010010", "1001001", "00010" and "0" are good but garlands "00101001", "1000001" and "01001100" are not. Note that the garland is not cyclic, i.e. the first turned on lamp is not going after the last turned on lamp and vice versa.

Your task is to find the minimum number of moves you need to make to obtain $k$-periodic garland from the given one.

You have to answer $t$ independent test cases.

-----Input-----

The first line of the input contains one integer $t$ ($1 \le t \le 25~ 000$) — the number of test cases. Then $t$ test cases follow.

The first line of the test case contains two integers $n$ and $k$ ($1 \le n \le 10^6; 1 \le k \le n$) — the length of $s$ and the required period. The second line of the test case contains the string $s$ consisting of $n$ characters '0' and '1'.

It is guaranteed that the sum of $n$ over all test cases does not exceed $10^6$ ($\sum n \le 10^6$).

-----Output-----

For each test case, print the answer — the minimum number of moves you need to make to obtain $k$-periodic garland from the given one.

-----Example-----
Input
6
9 2
010001010
9 3
111100000
7 4
1111111
10 3
1001110101
1 1
1
1 1
0

Output
1
2
5
4
0
0

def solve_garland (n k : Nat) (s : String) : Nat := sorry

def is_valid_garland (n k : Nat) (s : String) : Bool := sorry

def count_zeros (s : String) : Nat := sorry 

def all_ones (s : String) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded
