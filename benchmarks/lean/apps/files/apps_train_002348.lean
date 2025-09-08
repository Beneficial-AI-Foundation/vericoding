/-
Given an array A of integers, return true if and only if it is a valid mountain array.
Recall that A is a mountain array if and only if:

A.length >= 3
There exists some i with 0 < i < A.length - 1 such that:

A[0] < A[1] < ... A[i-1] < A[i] 
A[i] > A[i+1] > ... > A[A.length - 1]

Example 1:
Input: [2,1]
Output: false

Example 2:
Input: [3,5,5]
Output: false

Example 3:
Input: [0,3,2,1]
Output: true

Note:

0 <= A.length <= 10000
0 <= A[i] <= 10000
-/

-- <vc-helpers>
-- </vc-helpers>

def valid_mountain_array (arr: List Int) : Bool := sorry

theorem too_short_array {arr : List Int} 
  (h : arr.length ≤ 2) : 
  valid_mountain_array arr = false := sorry

theorem flat_array {arr : List Int} {n : Nat}
  (h1 : arr.length = n)
  (h2 : n ≥ 3) 
  (h3 : ∀ i j, i < n → j < n → arr.get! i = arr.get! j) :
  valid_mountain_array arr = false := sorry

theorem strictly_increasing {arr : List Int} {n : Nat}
  (h1 : arr.length = n)
  (h2 : n ≥ 3)
  (h3 : ∀ i j, i < j → j < n → arr.get! i < arr.get! j) :
  valid_mountain_array arr = false := sorry

theorem strictly_decreasing {arr : List Int} {n : Nat}
  (h1 : arr.length = n)
  (h2 : n ≥ 3)  
  (h3 : ∀ i j, i < j → j < n → arr.get! i > arr.get! j) :
  valid_mountain_array arr = false := sorry

theorem valid_mountain {arr : List Int} {n peak_idx : Nat}
  (h1 : arr.length = n)
  (h2 : n ≥ 3)
  (h3 : peak_idx = n / 2)
  (h4 : ∀ i j, i < j → j < peak_idx → arr.get! i < arr.get! j)
  (h5 : ∀ i j, peak_idx < i → i < j → j < n → arr.get! i > arr.get! j)
  (h6 : ∀ i j, i ≠ j → i < n → j < n → arr.get! i ≠ arr.get! j) :
  valid_mountain_array arr = true := sorry

/-
info: False
-/
-- #guard_msgs in
-- #eval valid_mountain_array [2, 1]

/-
info: False
-/
-- #guard_msgs in
-- #eval valid_mountain_array [3, 5, 5]

/-
info: True
-/
-- #guard_msgs in
-- #eval valid_mountain_array [0, 3, 2, 1]

-- Apps difficulty: introductory
-- Assurance level: unguarded