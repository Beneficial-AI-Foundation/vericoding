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
-- </vc-theorems>