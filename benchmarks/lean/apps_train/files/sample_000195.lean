Given an unsorted array of integers, find the length of the longest consecutive elements sequence.

Your algorithm should run in O(n) complexity.

Example:

Input: [100, 4, 200, 1, 3, 2]
Output: 4
Explanation: The longest consecutive elements sequence is [1, 2, 3, 4]. Therefore its length is 4.

def longest_consecutive (nums : List Int) : Nat := sorry

theorem output_nonnegative (nums : List Int) : 
  longest_consecutive nums ≥ 0 := sorry

def removeDuplicates (nums : List Int) : List Int := sorry

theorem same_as_deduplicated (nums : List Int) :
  longest_consecutive nums = longest_consecutive (removeDuplicates nums) := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded