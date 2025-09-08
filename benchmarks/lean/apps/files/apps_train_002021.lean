/-
You are given an array $a$ consisting of $n$ non-negative integers. You have to choose a non-negative integer $x$ and form a new array $b$ of size $n$ according to the following rule: for all $i$ from $1$ to $n$, $b_i = a_i \oplus x$ ($\oplus$ denotes the operation bitwise XOR).

An inversion in the $b$ array is a pair of integers $i$ and $j$ such that $1 \le i < j \le n$ and $b_i > b_j$.

You should choose $x$ in such a way that the number of inversions in $b$ is minimized. If there are several options for $x$ — output the smallest one.

-----Input-----

First line contains a single integer $n$ ($1 \le n \le 3 \cdot 10^5$) — the number of elements in $a$.

Second line contains $n$ space-separated integers $a_1$, $a_2$, ..., $a_n$ ($0 \le a_i \le 10^9$), where $a_i$ is the $i$-th element of $a$.

-----Output-----

Output two integers: the minimum possible number of inversions in $b$, and the minimum possible value of $x$, which achieves those number of inversions.

-----Examples-----
Input
4
0 1 3 2

Output
1 0

Input
9
10 7 9 10 7 5 5 3 5

Output
4 14

Input
3
8 10 3

Output
0 8

-----Note-----

In the first sample it is optimal to leave the array as it is by choosing $x = 0$.

In the second sample the selection of $x = 14$ results in $b$: $[4, 9, 7, 4, 9, 11, 11, 13, 11]$. It has $4$ inversions:

  $i = 2$, $j = 3$;  $i = 2$, $j = 4$;  $i = 3$, $j = 4$;  $i = 8$, $j = 9$. 

In the third sample the selection of $x = 8$ results in $b$: $[0, 2, 11]$. It has no inversions.
-/

-- <vc-helpers>
-- </vc-helpers>

def solve_inversions (n : Nat) (arr : List Nat) : Nat × Nat :=
  sorry

theorem solve_inversions_output_nat (n : Nat) (arr : List Nat) :
  let (inv, out) := solve_inversions n arr
  Nat.zero ≤ inv ∧ Nat.zero ≤ out :=
  sorry

theorem solve_inversions_deterministic (n : Nat) (arr : List Nat) :
  let res1 := solve_inversions n arr
  let res2 := solve_inversions n arr
  res1 = res2 :=
  sorry

structure Sorted (l : List Nat) : Prop where
  sorted : ∀ i j, i < j → j < l.length → 
    match l.get? i, l.get? j with
    | some x, some y => x ≤ y
    | _, _ => True

theorem sorted_array_zero_inversions (n : Nat) (arr sorted : List Nat) :
  Sorted sorted →
  List.length sorted = n →
  let (inv, _) := solve_inversions n sorted
  inv = 0 :=
  sorry

/-
info: (1, 0)
-/
-- #guard_msgs in
-- #eval solve_inversions 4 arr1.copy()

/-
info: (4, 14)
-/
-- #guard_msgs in
-- #eval solve_inversions 9 arr2.copy()

/-
info: (0, 8)
-/
-- #guard_msgs in
-- #eval solve_inversions 3 arr3.copy()

-- Apps difficulty: competition
-- Assurance level: unguarded