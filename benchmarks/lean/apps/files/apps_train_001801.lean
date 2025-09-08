/-
On the first row, we write a 0. Now in every subsequent row, we look at the previous row and replace each occurrence of 0 with 01, and each occurrence of 1 with 10.

Given row N and index K, return the K-th indexed symbol in row N. (The values of K are 1-indexed.) (1 indexed).

Examples:
Input: N = 1, K = 1
Output: 0

Input: N = 2, K = 1
Output: 0

Input: N = 2, K = 2
Output: 1

Input: N = 4, K = 5
Output: 1

Explanation:
row 1: 0
row 2: 01
row 3: 0110
row 4: 01101001

Note:

       N will be an integer in the range [1, 30].
       K will be an integer in the range [1, 2^(N-1)].
-/

def kthSymbol (n : Nat) (k : Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def countOnes (n : Nat) : Nat :=
  sorry

theorem first_row_is_zero (k : Nat) (h : k > 0) :
  kthSymbol 1 k = 0 :=
  sorry

theorem output_is_binary (n k : Nat) (h1 : n > 0) (h2 : k > 0) :
  kthSymbol n k = 0 ∨ kthSymbol n k = 1 :=
  sorry

theorem first_position_zero (n : Nat) (h : n > 1) :
  kthSymbol n 1 = 0 :=
  sorry

theorem kth_symbol_property (n k : Nat) (h1 : n > 0) (h2 : k > 0) :
  kthSymbol n k = if n > 1 then countOnes (k-1) % 2 else 0 :=
  sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval kth_symbol 1 1

/-
info: 0
-/
-- #guard_msgs in
-- #eval kth_symbol 2 1

/-
info: 1
-/
-- #guard_msgs in
-- #eval kth_symbol 4 5

-- Apps difficulty: interview
-- Assurance level: guarded