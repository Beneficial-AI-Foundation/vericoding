/-
# Task
 You are given integer `n` determining set S = {1, 2, ..., n}. Determine if the number of k-element subsets of S is `ODD` or `EVEN` for given integer k.

# Example

 For `n = 3, k = 2`, the result should be `"ODD"`

 In this case, we have 3 2-element subsets of {1, 2, 3}:

 `{1, 2}, {1, 3}, {2, 3}`

 For `n = 2, k = 1`, the result should be `"EVEN"`.

 In this case, we have 2 1-element subsets of {1, 2}:

 `{1}, {2}`

 `Don't bother with naive solution - numbers here are really big.`

# Input/Output

 - `[input]` integer `n`

    `1 <= n <= 10^9`

 - `[input]` integer `k`

    `1 <= k <= n`

 - `[output]` a string

    `"EVEN"` or `"ODD"` depending if the number of k-element subsets of S = {1, 2, ..., n} is ODD or EVEN.
-/

-- <vc-helpers>
-- </vc-helpers>

def subsets_parity (n k : Nat) : String := sorry

def choose (n k : Nat) : Nat := sorry

theorem subset_parity_full_set (n : Nat) (h : n > 0) : 
  subsets_parity n n = "ODD" := sorry

theorem subset_parity_empty_set (n : Nat) (h : n > 0) :
  subsets_parity n 0 = "ODD" := sorry

theorem valid_subset_parity (n k : Nat) (h1 : n > 0) (h2 : k ≤ n) :
  (subsets_parity n k = "ODD" ↔ choose n k % 2 = 1) ∧
  (subsets_parity n k = "EVEN" ↔ choose n k % 2 = 0) := sorry

theorem valid_subset_result (n k : Nat) (h1 : n > 0) (h2 : k ≤ n) :
  subsets_parity n k = "ODD" ∨ subsets_parity n k = "EVEN" := sorry

/-
info: 'ODD'
-/
-- #guard_msgs in
-- #eval subsets_parity 3 2

/-
info: 'EVEN'
-/
-- #guard_msgs in
-- #eval subsets_parity 2 1

/-
info: 'EVEN'
-/
-- #guard_msgs in
-- #eval subsets_parity 20 10

-- Apps difficulty: interview
-- Assurance level: unguarded