/-
Given an integer array nums, find the contiguous subarray within an array (containing at least one number) which has the largest product.

Example 1:

Input: [2,3,-2,4]
Output: 6
Explanation: [2,3] has the largest product 6.

Example 2:

Input: [-2,0,-1]
Output: 0
Explanation: The result cannot be 2, because [-2,-1] is not a subarray.
-/

def maxProduct (nums : List Int) : Int := sorry

def listMax (xs : List Int) : Int :=
  match xs with
  | [] => 0
  | h :: t => List.foldl max h t

-- <vc-helpers>
-- </vc-helpers>

def listProd (xs : List Int) : Int :=
  match xs with
  | [] => 1
  | h :: t => List.foldl (· * ·) h t

theorem maxProduct_empty_list :
  maxProduct [] = 0 := sorry

theorem maxProduct_single_element (x : Int) :
  maxProduct [x] = x := sorry

theorem maxProduct_nonneg_with_zero (nums : List Int) :
  (0 ∈ nums) → maxProduct nums ≥ 0 := sorry

/-
info: 6
-/
-- #guard_msgs in
-- #eval maxProduct [2, 3, -2, 4]

/-
info: 0
-/
-- #guard_msgs in
-- #eval maxProduct [-2, 0, -1]

/-
info: 24
-/
-- #guard_msgs in
-- #eval maxProduct [-2, 3, -4]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible