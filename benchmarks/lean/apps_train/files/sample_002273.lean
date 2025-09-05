This is a hard version of the problem. In this version, the given array can contain equal elements and the constraints on $n$ are greater than in the easy version of the problem.

You are given an array $a$ of $n$ integers (the given array can contain equal elements). You can perform the following operations on array elements:  choose any index $i$ ($1 \le i \le n$) and move the element $a[i]$ to the begin of the array;  choose any index $i$ ($1 \le i \le n$) and move the element $a[i]$ to the end of the array. 

For example, if $n = 5$, $a = [4, 7, 2, 2, 9]$, then the following sequence of operations can be performed:   after performing the operation of the first type to the second element, the array $a$ will become $[7, 4, 2, 2, 9]$;  after performing the operation of the second type to the second element, the array $a$ will become $[7, 2, 2, 9, 4]$. 

You can perform operations of any type any number of times in any order.

Find the minimum total number of operations of the first and second type that will make the $a$ array sorted in non-decreasing order. In other words, what is the minimum number of operations must be performed so the array satisfies the inequalities $a[1] \le a[2] \le \ldots \le a[n]$.

-----Input-----

The first line contains a single integer $t$ ($1 \le t \le 10^4$) — the number of test cases in the test. Then $t$ test cases follow.

Each test case starts with a line containing an integer $n$ ($1 \le n \le 2 \cdot 10^5$) — the size of the array $a$.

Then follow $n$ integers $a_1, a_2, \ldots, a_n$ ($0 \le a_i \le 10^9$) — an array that needs to be sorted by the given operations. The given array can contain equal elements.

The sum of $n$ for all test cases in one test does not exceed $2 \cdot 10^5$.

-----Output-----

For each test case output one integer — the minimum total number of operations of the first and second type, which will make the array sorted in non-decreasing order.

-----Example-----
Input
9
5
4 7 2 2 9
5
3 5 8 1 7
5
1 2 2 4 5
2
0 1
3
0 1 0
4
0 1 0 0
4
0 1 0 1
4
0 1 0 2
20
16 15 1 10 0 14 0 10 3 9 2 5 4 5 17 9 10 20 0 9

Output
2
2
0
0
1
1
1
1
16

-----Note-----

In the first test case, you first need to move two 2, to the beginning of the array. Therefore, the desired sequence of operations: $[4, 7, 2, 2, 9] \rightarrow [2, 4, 7, 2, 9] \rightarrow [2, 2, 4, 7, 9]$.

In the second test case, you need to move the 1 to the beginning of the array, and the 8 — to the end. Therefore, the desired sequence of operations: $[3, 5, 8, 1, 7] \rightarrow [1, 3, 5, 8, 7] \rightarrow [1, 3, 5, 7, 8]$.

In the third test case, the array is already sorted.

def min_ops_to_sort {α : Type u} [Ord α] (arr : List α) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible
