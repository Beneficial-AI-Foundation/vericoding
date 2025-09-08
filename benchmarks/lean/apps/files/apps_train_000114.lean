/-
Let's call an array $a_1, a_2, \dots, a_m$ of nonnegative integer numbers good if $a_1 + a_2 + \dots + a_m = 2\cdot(a_1 \oplus a_2 \oplus \dots \oplus a_m)$, where $\oplus$ denotes the bitwise XOR operation.

For example, array $[1, 2, 3, 6]$ is good, as $1 + 2 + 3 + 6 = 12 = 2\cdot 6 = 2\cdot (1\oplus 2 \oplus 3 \oplus 6)$. At the same time, array $[1, 2, 1, 3]$ isn't good, as $1 + 2 + 1 + 3 = 7 \neq 2\cdot 1 = 2\cdot(1\oplus 2 \oplus 1 \oplus 3)$.

You are given an array of length $n$: $a_1, a_2, \dots, a_n$. Append at most $3$ elements to it to make it good. Appended elements don't have to be different. It can be shown that the solution always exists under the given constraints. If there are different solutions, you are allowed to output any of them. Note that you don't have to minimize the number of added elements!. So, if an array is good already you are allowed to not append elements.

-----Input-----

Each test contains multiple test cases. The first line contains the number of test cases $t$ ($1 \le t \le 10\,000$). The description of the test cases follows.

The first line of each test case contains a single integer $n$ $(1\le n \le 10^5)$ — the size of the array.

The second line of each test case contains $n$ integers $a_1, a_2, \dots, a_n$ ($0\le a_i \le 10^9$) — the elements of the array.

It is guaranteed that the sum of $n$ over all test cases does not exceed $10^5$.

-----Output-----

For each test case, output two lines.

In the first line, output a single integer $s$ ($0\le s\le 3$) — the number of elements you want to append.

In the second line, output $s$ integers $b_1, \dots, b_s$ ($0\le b_i \le 10^{18}$) — the elements you want to append to the array.

If there are different solutions, you are allowed to output any of them.

-----Example-----
Input
3
4
1 2 3 6
1
8
2
1 1

Output
0

2
4 4
3
2 6 2

-----Note-----

In the first test case of the example, the sum of all numbers is $12$, and their $\oplus$ is $6$, so the condition is already satisfied.

In the second test case of the example, after adding $4, 4$, the array becomes $[8, 4, 4]$. The sum of numbers in it is $16$, $\oplus$ of numbers in it is $8$.
-/

def solve_xor_sum (n : Nat) (arr : List Nat) : List Nat := sorry

def xor_fold (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | h::t => t.foldl Nat.xor h

-- <vc-helpers>
-- </vc-helpers>

def list_sum (l : List Nat) : Nat := 
  match l with
  | [] => 0
  | h::t => h + list_sum t

theorem solve_xor_sum_length {n : Nat} {arr : List Nat} :
  arr ≠ [] →
  let result := solve_xor_sum n arr
  List.length result = 0 ∨ List.length result = 2 := sorry

theorem solve_xor_sum_verifies {n : Nat} {arr : List Nat} :
  arr ≠ [] →
  let result := solve_xor_sum n arr
  let full_arr := arr ++ result
  list_sum full_arr = 2 * xor_fold full_arr := sorry

theorem solve_xor_sum_bounds {n : Nat} {arr : List Nat} :
  arr ≠ [] →
  let result := solve_xor_sum n arr
  let total := list_sum arr
  ∀ x ∈ result, x ≥ 0 ∧ x ≤ 2 * total := sorry

/-
info: []
-/
-- #guard_msgs in
-- #eval solve_xor_sum 4 [1, 2, 3, 6]

/-
info: 2
-/
-- #guard_msgs in
-- #eval len solve_xor_sum(1, [8])

/-
info: 2 * (arr[0] ^ arr[1] ^ arr[2])
-/
-- #guard_msgs in
-- #eval sum [8] + result

/-
info: 2 * xor
-/
-- #guard_msgs in
-- #eval sum [1, 1] + result

-- Apps difficulty: interview
-- Assurance level: unguarded