def maxSumDivThree (nums: List Nat) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def sum (nums: List Nat) : Nat :=
  sorry

theorem maxSumDivThree_divisible_by_3 (nums: List Nat) :
  maxSumDivThree nums % 3 = 0 :=
  sorry

theorem maxSumDivThree_bounded (nums: List Nat) :
  maxSumDivThree nums ≤ sum nums :=
  sorry

theorem maxSumDivThree_nonnegative (nums: List Nat) :
  maxSumDivThree nums ≥ 0 :=
  sorry

theorem maxSumDivThree_all_divisible (nums: List Nat) 
  (h: ∀ n ∈ nums, n % 3 = 0) :
  maxSumDivThree nums = sum nums :=
  sorry

theorem maxSumDivThree_none_divisible (nums: List Nat)
  (h1: nums ≠ []) 
  (h2: ∀ n ∈ nums, n % 3 ≠ 0) :
  maxSumDivThree nums ≤ sum nums ∧ 
  maxSumDivThree nums % 3 = 0 :=
  sorry

theorem maxSumDivThree_monotonic (nums: List Nat) :
  maxSumDivThree nums ≤ maxSumDivThree (nums ++ [3]) :=
  sorry

/-
info: 18
-/
-- #guard_msgs in
-- #eval maxSumDivThree [3, 6, 5, 1, 8]

/-
info: 0
-/
-- #guard_msgs in
-- #eval maxSumDivThree [4]

/-
info: 12
-/
-- #guard_msgs in
-- #eval maxSumDivThree [1, 2, 3, 4, 4]

-- Apps difficulty: interview
-- Assurance level: guarded