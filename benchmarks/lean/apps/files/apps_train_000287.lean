/-
The n-queens puzzle is the problem of placing n queens on an n×n chessboard such that no two queens attack each other.

Given an integer n, return the number of distinct solutions to the n-queens puzzle.

Example:

Input: 4
Output: 2
Explanation: There are two distinct solutions to the 4-queens puzzle as shown below.
[
 [".Q..",  // Solution 1
  "...Q",
  "Q...",
  "..Q."],

 ["..Q.",  // Solution 2
  "Q...",
  "...Q",
  ".Q.."]
]
-/

-- <vc-helpers>
-- </vc-helpers>

def total_n_queens (n: Nat) : Nat := sorry 

theorem total_n_queens_nonneg (n: Nat) : 
  total_n_queens n ≥ 0 := sorry

theorem total_n_queens_unique :
  ∀ n₁ n₂, 
  n₁ = n₂ → total_n_queens n₁ = total_n_queens n₂ := sorry

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible