/-
You are given n strings s_1, s_2, ..., s_{n} consisting of characters 0 and 1. m operations are performed, on each of them you concatenate two existing strings into a new one. On the i-th operation the concatenation s_{a}_{i}s_{b}_{i} is saved into a new string s_{n} + i (the operations are numbered starting from 1). After each operation you need to find the maximum positive integer k such that all possible strings consisting of 0 and 1 of length k (there are 2^{k} such strings) are substrings of the new string. If there is no such k, print 0.

-----Input-----

The first line contains single integer n (1 ≤ n ≤ 100) — the number of strings. The next n lines contain strings s_1, s_2, ..., s_{n} (1 ≤ |s_{i}| ≤ 100), one per line. The total length of strings is not greater than 100.

The next line contains single integer m (1 ≤ m ≤ 100) — the number of operations. m lines follow, each of them contains two integers a_{i} abd b_{i} (1 ≤ a_{i}, b_{i} ≤ n + i - 1) — the number of strings that are concatenated to form s_{n} + i.

-----Output-----

Print m lines, each should contain one integer — the answer to the question after the corresponding operation.

-----Example-----
Input
5
01
10
101
11111
0
3
1 2
6 5
4 4

Output
1
2
0

-----Note-----

On the first operation, a new string "0110" is created. For k = 1 the two possible binary strings of length k are "0" and "1", they are substrings of the new string. For k = 2 and greater there exist strings of length k that do not appear in this string (for k = 2 such string is "00"). So the answer is 1.

On the second operation the string "01100" is created. Now all strings of length k = 2 are present.

On the third operation the string "1111111111" is created. There is no zero, so the answer is 0.
-/

-- <vc-helpers>
-- </vc-helpers>

def BinaryString := String

def solve_binary_string_concat (strings : List BinaryString) (operations : List (Nat × Nat)) : List Nat := sorry

theorem solve_binary_string_concat_basic_properties 
  (strings : List BinaryString) 
  (operations : List (Nat × Nat))
  (h1 : strings.length ≥ 2)
  (h2 : strings.length ≤ 5) 
  (h3 : operations.length ≥ 1)
  (h4 : operations.length ≤ 3)
  (h5 : ∀ s ∈ strings, s.length ≥ 1)
  (h6 : ∀ s ∈ strings, s.length ≤ 20)
  (h7 : ∀ s ∈ strings, ∀ c ∈ s.data, c = '0' ∨ c = '1')
  (h8 : ∀ op ∈ operations, op.1 ≥ 1 ∧ op.1 ≤ strings.length ∧ op.2 ≥ 1 ∧ op.2 ≤ strings.length) :
  let result := solve_binary_string_concat strings operations
  (∀ x ∈ result, x ≥ 0) ∧
  (result.length = operations.length) ∧
  (∀ x ∈ result, x ≤ 20) := sorry

theorem solve_binary_string_concat_all_zeros
  (strings : List BinaryString)
  (h1 : strings.length ≥ 2)
  (h2 : strings.length ≤ 5)
  (h3 : ∀ s ∈ strings, s = "0") :
  solve_binary_string_concat strings [(1,2)] = [0] := sorry

theorem solve_binary_string_concat_all_ones
  (strings : List BinaryString)
  (h1 : strings.length ≥ 2)
  (h2 : strings.length ≤ 5)
  (h3 : ∀ s ∈ strings, s = "1") :
  solve_binary_string_concat strings [(1,2)] = [0] := sorry

/-
info: [1, 2, 0]
-/
-- #guard_msgs in
-- #eval solve_binary_string_concat ["01", "10", "101", "11111", "0"] [(1, 2), (6, 5), (4, 4)]

/-
info: [1, 1, 1, 2, 1, 2]
-/
-- #guard_msgs in
-- #eval solve_binary_string_concat ["01", "1", "0011", "0", "01"] [(5, 5), (3, 2), (4, 2), (6, 7), (5, 1), (9, 7)]

/-
info: [1]
-/
-- #guard_msgs in
-- #eval solve_binary_string_concat ["0", "1"] [(1, 2)]

-- Apps difficulty: competition
-- Assurance level: unguarded