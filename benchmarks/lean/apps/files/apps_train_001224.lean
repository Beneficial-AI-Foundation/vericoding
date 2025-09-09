/-
Chef likes problems related to learning new languages. He only knows first N letters of English alphabet. Also he explores all M-letter words formed by the characters he knows. Define cost for a given M-letter word S, cost(S) = P1, S1+P2, S2+...+PM, SM, where Pi, j is i, jth entry of matrix P. Sort all the words by descending cost, if costs are equal, sort them lexicographically. You need to find K-th M-letter word in Chef's order.

-----Input-----
First line contains three positive integer numbers N, M and K.
Next M lines contains N integers per line, denoting the matrix P.

-----Output-----
Output in a single line K-th M-letter in Chef's order.

-----Constraints-----
- 1 ≤ N ≤ 16 
- 1 ≤ M ≤ 10 
- 1 ≤ K ≤ NM
- 0 ≤ Pi, j ≤ 109

-----Subtasks-----
- Subtask #1: (20 points) 1 ≤ K ≤ 10000
- Subtask #2: (20 points) 1 ≤ M ≤ 5
- Subtask #3: (60 points) Original constraints

-----Example-----
Input:2 5 17
7 9
13 18
10 12
4 18
3 9

Output:aaaba
-/

-- <vc-helpers>
-- </vc-helpers>

def find_kth_word (N M K : Nat) (P : List (List Nat)) : String := sorry

theorem minimal_case (N : Nat) (h : 1 ≤ N) (h' : N ≤ 3) : 
  let result := find_kth_word N 1 1 [[1]]
  String.length result = 1 ∧ result = "a" := sorry

theorem edge_cases (N M : Nat) (hN : 2 ≤ N) (hN' : N ≤ 3) (hM : 2 ≤ M) (hM' : M ≤ 3) :
  let result := find_kth_word N M N (List.replicate M (List.replicate N 1))
  String.length result = M ∧ 
  ∀ c ∈ result.data, 'a'.toNat ≤ c.toNat ∧ c.toNat ≤ 'a'.toNat + N - 1 := sorry

theorem given_cases : 
  find_kth_word 2 5 17 [[7,9], [13,18], [10,12], [4,18], [3,9]] = "aaaba" ∧
  find_kth_word 1 1 1 [[5]] = "a" := sorry

/-
info: 'aaaba'
-/
-- #guard_msgs in
-- #eval find_kth_word 2 5 17 [[7, 9], [13, 18], [10, 12], [4, 18], [3, 9]]

/-
info: 'a'
-/
-- #guard_msgs in
-- #eval find_kth_word 1 1 1 [[5]]

-- Apps difficulty: interview
-- Assurance level: unguarded