You are given an array $a$ consisting of $n$ integers.

In one move, you can choose some index $i$ ($1 \le i \le n - 2$) and shift the segment $[a_i, a_{i + 1}, a_{i + 2}]$ cyclically to the right (i.e. replace the segment $[a_i, a_{i + 1}, a_{i + 2}]$ with $[a_{i + 2}, a_i, a_{i + 1}]$). 

Your task is to sort the initial array by no more than $n^2$ such operations or say that it is impossible to do that.

You have to answer $t$ independent test cases.

-----Input-----

The first line of the input contains one integer $t$ ($1 \le t \le 100$) — the number of test cases. Then $t$ test cases follow.

The first line of the test case contains one integer $n$ ($3 \le n \le 500$) — the length of $a$. The second line of the test case contains $n$ integers $a_1, a_2, \dots, a_n$ ($1 \le a_i \le 500$), where $a_i$ is the $i$-th element $a$.

It is guaranteed that the sum of $n$ does not exceed $500$.

-----Output-----

For each test case, print the answer: -1 on the only line if it is impossible to sort the given array using operations described in the problem statement, or the number of operations $ans$ on the first line and $ans$ integers $idx_1, idx_2, \dots, idx_{ans}$ ($1 \le idx_i \le n - 2$), where $idx_i$ is the index of left border of the segment for the $i$-th operation. You should print indices in order of performing operations.

-----Example-----
Input
5
5
1 2 3 4 5
5
5 4 3 2 1
8
8 4 5 2 3 6 7 3
7
5 2 1 6 4 7 3
6
1 2 3 3 6 4

Output
0

6
3 1 3 2 2 3 
13
2 1 1 6 4 2 4 3 3 4 4 6 6 
-1
4
3 3 4 4

def solve_array_sort (n : Nat) (arr : List Nat) : List Nat := sorry

def List.sort (l : List Nat) : List Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
