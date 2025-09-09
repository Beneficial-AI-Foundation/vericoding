/-
Given an array A of integers, return the number of (contiguous, non-empty) subarrays that have a sum divisible by K.

Example 1:
Input: A = [4,5,0,-2,-3,1], K = 5
Output: 7
Explanation: There are 7 subarrays with a sum divisible by K = 5:
[4, 5, 0, -2, -3, 1], [5], [5, 0], [5, 0, -2, -3], [0], [0, -2, -3], [-2, -3]

Note:

1 <= A.length <= 30000
-10000 <= A[i] <= 10000
2 <= K <= 10000
-/

-- <vc-helpers>
-- </vc-helpers>

def subarraysDivByK (nums : List Int) (k : Int) : Int := sorry

def countSubarraysDivisibleByK (nums : List Int) (k : Int) (i : Nat) (sum : Int) (count : Int) : Int :=
  if h : i < nums.length then
    let newSum := sum + nums[i]'h
    if newSum % k = 0 then
      countSubarraysDivisibleByK nums k (i + 1) newSum (count + 1)
    else  
      countSubarraysDivisibleByK nums k (i + 1) newSum count
  else
    count
termination_by nums.length - i

theorem single_element_divisible (k : Int)
  (h : k > 0) :
  subarraysDivByK [k] k = 1 := sorry

/-
info: 7
-/
-- #guard_msgs in
-- #eval subarraysDivByK [4, 5, 0, -2, -3, 1] 5

/-
info: 1
-/
-- #guard_msgs in
-- #eval subarraysDivByK [5] 5

/-
info: 9
-/
-- #guard_msgs in
-- #eval subarraysDivByK [4, 5, 0, -2, -3, 1, 5] 5

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible