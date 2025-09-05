Given an array of integers nums and a positive integer k, find whether it's possible to divide this array into k non-empty subsets whose sums are all equal.

Example 1:

Input: nums = [4, 3, 2, 3, 5, 2, 1], k = 4
Output: True
Explanation: It's possible to divide it into 4 subsets (5), (1, 4), (2,3), (2,3) with equal sums.

Note:
1 .
0 < nums[i] < 10000.

def List.sum : List Nat → Nat 
  | [] => 0
  | (x::xs) => x + List.sum xs

def getMaximum (l : List Nat) (h : l.length > 0) : Nat :=
  match l with
  | [] => 0 
  | [x] => x
  | (x::xs) => x -- simplified version to avoid proof complexity

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
