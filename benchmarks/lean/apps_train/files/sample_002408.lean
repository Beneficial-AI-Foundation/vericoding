Given an unsorted array of integers, find the length of longest continuous increasing subsequence (subarray).

Example 1:

Input: [1,3,5,4,7]
Output: 3
Explanation: The longest continuous increasing subsequence is [1,3,5], its length is 3. 
Even though [1,3,5,7] is also an increasing subsequence, it's not a continuous one where 5 and 7 are separated by 4. 

Example 2:

Input: [2,2,2,2,2]
Output: 1
Explanation: The longest continuous increasing subsequence is [2], its length is 1. 

Note:
Length of the array will not exceed 10,000.

def find_length_of_lcis (nums : List Int) : Nat := sorry

theorem lcis_length_properties (nums : List Int) : 
  let result := find_length_of_lcis nums
  result ≥ 0 ∧ 
  result ≤ nums.length ∧
  (nums.length = 0 → result = 0) ∧ 
  (nums.length > 0 → result ≥ 1) := sorry

def is_strictly_increasing (nums : List Int) (i : Nat) : Bool :=
  i > 0 && i < nums.length && nums[i]! > nums[i-1]!

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible