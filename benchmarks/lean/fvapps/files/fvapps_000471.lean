-- <vc-preamble>
def abs (x : Int) : Int :=
  if x < 0 then -x else x
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def threeSumClosest (nums : List Int) (target : Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem threeSumClosest_is_sum_of_three {nums : List Int} {target : Int}
  (h : nums.length ≥ 3) :
  ∃ i j k, i < j ∧ j < k ∧ k < nums.length ∧ 
    threeSumClosest nums target = nums[i]! + nums[j]! + nums[k]! :=
  sorry

theorem threeSumClosest_is_closest {nums : List Int} {target : Int} 
  (h : nums.length ≥ 3) :
  ∀ i j k, i < j → j < k → k < nums.length →
    (abs (threeSumClosest nums target - target)) ≤ 
    (abs (nums[i]! + nums[j]! + nums[k]! - target)) :=
  sorry

theorem threeSumClosest_all_ones : 
  threeSumClosest [1,1,1] 0 = 3 :=
  sorry

theorem threeSumClosest_all_neg_ones :
  threeSumClosest [-1,-1,-1] 0 = -3 :=
  sorry

theorem threeSumClosest_all_zeros :
  threeSumClosest [0,0,0] 1 = 0 :=
  sorry

theorem threeSumClosest_insufficient_nums {nums : List Int} 
  (h : nums.length < 3) :
  threeSumClosest nums 0 = 0 :=
  sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval three_sum_closest [-4, -1, 1, 2] 1

/-
info: 3
-/
-- #guard_msgs in
-- #eval three_sum_closest [1, 1, 1, 0] 100

/-
info: 0
-/
-- #guard_msgs in
-- #eval three_sum_closest [0, 2, 1, -3] 1
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded