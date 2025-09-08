/-
Given an unsorted array return whether an increasing subsequence of length 3 exists or not in the array.

Formally the function should:
Return true if there exists i, j, k  
such that arr[i] < arr[j] < arr[k] given 0 ≤ i < j < k ≤ n-1 
else return false.

Your algorithm should run in O(n) time complexity and O(1) space complexity.

Examples:
Given [1, 2, 3, 4, 5],
return true.

Given [5, 4, 3, 2, 1],
return false.

Credits:Special thanks to @DjangoUnchained for adding this problem and creating all test cases.
-/

-- <vc-helpers>
-- </vc-helpers>

def has_increasing_triplet (nums : List Int) : Bool :=
  sorry

theorem has_increasing_triplet_matches_bruteforce (nums : List Int) (h : nums.length ≥ 3) :
  has_increasing_triplet nums = 
    (∃ i j k, i < j ∧ j < k ∧ k < nums.length ∧
     nums[i]! < nums[j]! ∧ nums[j]! < nums[k]!) :=
  sorry

theorem monotonic_decreasing_has_no_triplet (nums : List Int) (h : nums.length ≥ 3) :
  (∀ i j, i < j → j < nums.length → nums[j]! ≤ nums[i]!) →
  ¬(has_increasing_triplet nums) :=
  sorry

theorem monotonic_increasing_has_triplet (nums : List Int) 
  (h1 : nums.length ≥ 3)
  (h2 : ∀ i j, i < j → j < nums.length → nums[i]! ≤ nums[j]!)
  (h3 : ∀ x, (nums.countP (fun y => y = x)) ≤ 2) :
  has_increasing_triplet nums :=
  sorry

theorem short_lists_have_no_triplet (nums : List Int) (h : nums.length < 3) :
  ¬(has_increasing_triplet nums) :=
  sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval has_increasing_triplet [1, 2, 3, 4, 5]

/-
info: False
-/
-- #guard_msgs in
-- #eval has_increasing_triplet [5, 4, 3, 2, 1]

/-
info: True
-/
-- #guard_msgs in
-- #eval has_increasing_triplet [2, 1, 5, 0, 4, 6]

-- Apps difficulty: interview
-- Assurance level: unguarded