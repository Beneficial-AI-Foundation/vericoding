You are given an array of integers. Vasya can permute (change order) its integers. He wants to do it so that as many as possible integers will become on a place where a smaller integer used to stand. Help Vasya find the maximal number of such integers.

For instance, if we are given an array $[10, 20, 30, 40]$, we can permute it so that it becomes $[20, 40, 10, 30]$. Then on the first and the second positions the integers became larger ($20>10$, $40>20$) and did not on the third and the fourth, so for this permutation, the number that Vasya wants to maximize equals $2$. Read the note for the first example, there is one more demonstrative test case.

Help Vasya to permute integers in such way that the number of positions in a new array, where integers are greater than in the original one, is maximal.

-----Input-----

The first line contains a single integer $n$ ($1 \leq n \leq 10^5$) — the length of the array.

The second line contains $n$ integers $a_1, a_2, \ldots, a_n$ ($1 \leq a_i \leq 10^9$) — the elements of the array.

-----Output-----

Print a single integer — the maximal number of the array's elements which after a permutation will stand on the position where a smaller element stood in the initial array.

-----Examples-----
Input
7
10 1 1 1 5 5 3

Output
4

Input
5
1 1 1 1 1

Output
0

-----Note-----

In the first sample, one of the best permutations is $[1, 5, 5, 3, 10, 1, 1]$. On the positions from second to fifth the elements became larger, so the answer for this permutation is 4.

In the second sample, there is no way to increase any element with a permutation, so the answer is 0.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: guarded_and_plausible
