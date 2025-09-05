Consider all binary strings of length $m$ ($1 \le m \le 60$). A binary string is a string that consists of the characters 0 and 1 only. For example, 0110 is a binary string, and 012aba is not. Obviously, there are exactly $2^m$ such strings in total.

The string $s$ is lexicographically smaller than the string $t$ (both have the same length $m$) if in the first position $i$ from the left in which they differ, we have $s[i] < t[i]$. This is exactly the way strings are compared in dictionaries and in most modern programming languages when comparing them in a standard way. For example, the string 01011 is lexicographically smaller than the string 01100, because the first two characters are the same, and the third character in the first string is less than that in the second.

We remove from this set $n$ ($1 \le n \le \min(2^m-1, 100)$) distinct binary strings $a_1, a_2, \ldots, a_n$, each of length $m$. Thus, the set will have $k=2^m-n$ strings. Sort all strings of the resulting set in lexicographical ascending order (as in the dictionary).

We number all the strings after sorting from $0$ to $k-1$. Print the string whose index is $\lfloor \frac{k-1}{2} \rfloor$ (such an element is called median), where $\lfloor x \rfloor$ is the rounding of the number down to the nearest integer.

For example, if $n=3$, $m=3$ and $a=[$010, 111, 001$]$, then after removing the strings $a_i$ and sorting, the result will take the form: $[$000, 011, 100, 101, 110$]$. Thus, the desired median is 100.

-----Input-----

The first line contains an integer $t$ ($1 \le t \le 1000$) — the number of test cases. Then, $t$ test cases follow.

The first line of each test case contains integers $n$ ($1 \le n \le \min(2^m-1, 100)$) and $m$ ($1 \le m \le 60$), where $n$ is the number of strings to remove, and $m$ is the length of binary strings. The next $n$ lines contain $a_1, a_2, \ldots, a_n$ — distinct binary strings of length $m$.

The total length of all given binary strings in all test cases in one test does not exceed $10^5$.

-----Output-----

Print $t$ answers to the test cases. For each test case, print a string of length $m$ — the median of the sorted sequence of remaining strings in the corresponding test case.

-----Example-----
Input
5
3 3
010
001
111
4 3
000
111
100
011
1 1
1
1 1
0
3 2
00
01
10

Output
100
010
0
1
11

-----Note-----

The first test case is explained in the statement.

In the second test case, the result after removing strings and sorting is $[$001, 010, 101, 110$]$. Therefore, the desired median is 010.

def find_median_binary_string (n m : Nat) (removed : List String) : String := sorry

def isAllZeros (s : String) : Bool := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded