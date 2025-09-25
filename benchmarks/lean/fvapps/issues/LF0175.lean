-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
-- </vc-definitions>

-- <vc-theorems>
theorem output_size_bounds {nums : List Int} :
  longest_increasing_subsequence nums ≤ nums.length ∧ 
  longest_increasing_subsequence nums ≥ 0 := sorry

/- For a strictly increasing sequence of unique elements, result equals length -/  

theorem strictly_increasing_equals_length {nums : List Int} (h: nums.Nodup) : 
  (∀ i j, i < j → j < nums.length → nums.get! i < nums.get! j) →
  longest_increasing_subsequence nums = nums.length := sorry

/- For a strictly decreasing sequence of unique elements, result is 1 -/

theorem strictly_decreasing_equals_one {nums : List Int} (h: nums.Nodup) : 
  (∀ i j, i < j → j < nums.length → nums.get! i > nums.get! j) →
  longest_increasing_subsequence nums = 1 := sorry

/- Max result of sequence and its reverse are equal -/

theorem reverse_order_max {nums : List Int} :
  max (longest_increasing_subsequence nums) (longest_increasing_subsequence nums.reverse) =
  longest_increasing_subsequence nums ∨
  max (longest_increasing_subsequence nums) (longest_increasing_subsequence nums.reverse) =
  longest_increasing_subsequence nums.reverse := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval longest_increasing_subsequence [10, 9, 2, 5, 3, 7, 101, 18]

/-
info: 0
-/
-- #guard_msgs in
-- #eval longest_increasing_subsequence []

/-
info: 5
-/
-- #guard_msgs in
-- #eval longest_increasing_subsequence [1, 2, 3, 4, 5]
-- </vc-theorems>