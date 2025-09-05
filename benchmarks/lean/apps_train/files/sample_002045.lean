Vasya's got a birthday coming up and his mom decided to give him an array of positive integers a of length n.

Vasya thinks that an array's beauty is the greatest common divisor of all its elements. His mom, of course, wants to give him as beautiful an array as possible (with largest possible beauty). Unfortunately, the shop has only one array a left. On the plus side, the seller said that he could decrease some numbers in the array (no more than by k for each number).

The seller can obtain array b from array a if the following conditions hold: b_{i} > 0; 0 ≤ a_{i} - b_{i} ≤ k for all 1 ≤ i ≤ n.

Help mom find the maximum possible beauty of the array she will give to Vasya (that seller can obtain).

-----Input-----

The first line contains two integers n and k (1 ≤ n ≤ 3·10^5; 1 ≤ k ≤ 10^6). The second line contains n integers a_{i} (1 ≤ a_{i} ≤ 10^6) — array a.

-----Output-----

In the single line print a single number — the maximum possible beauty of the resulting array.

-----Examples-----
Input
6 1
3 6 10 12 13 16

Output
3

Input
5 3
8 21 52 15 77

Output
7

-----Note-----

In the first sample we can obtain the array:

3 6 9 12 12 15

In the second sample we can obtain the next array:

7 21 49 14 77

def get_max_beauty (n k : Nat) (arr : List Nat) : Nat :=
sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: guarded