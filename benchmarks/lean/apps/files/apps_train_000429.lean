/-
A subarray A[i], A[i+1], ..., A[j] of A is said to be turbulent if and only if:

For i <= k < j, A[k] > A[k+1] when k is odd, and A[k] < A[k+1] when k is even;
OR, for i <= k < j, A[k] > A[k+1] when k is even, and A[k] < A[k+1] when k is odd.

That is, the subarray is turbulent if the comparison sign flips between each adjacent pair of elements in the subarray.
Return the length of a maximum size turbulent subarray of A.

Example 1:
Input: [9,4,2,10,7,8,8,1,9]
Output: 5
Explanation: (A[1] > A[2] < A[3] > A[4] < A[5])

Example 2:
Input: [4,8,12,16]
Output: 2

Example 3:
Input: [100]
Output: 1

Note:

1 <= A.length <= 40000
0 <= A[i] <= 10^9
-/

-- <vc-helpers>
-- </vc-helpers>

def max_turbulence_size (arr : List Int) : Nat :=
  sorry

theorem turbulence_size_bounds {arr : List Int} (h : arr.length ≥ 1) : 
  1 ≤ max_turbulence_size arr ∧ max_turbulence_size arr ≤ arr.length :=
  sorry

theorem same_elements_turbulence {arr : List Int} (h : arr.length ≥ 1) :
  let same := List.replicate arr.length (arr.get ⟨0, by exact Nat.zero_lt_of_lt h⟩)
  max_turbulence_size same = 1 :=
  sorry

theorem strictly_increasing_turbulence {arr : List Int} (h : arr.length ≥ 2) :
  max_turbulence_size arr = 2 :=
  sorry

theorem single_element_turbulence {arr : List Int} (h : arr.length ≥ 1) :
  max_turbulence_size [arr.get ⟨0, by exact Nat.zero_lt_of_lt h⟩] = 1 :=
  sorry

theorem pair_turbulence {arr : List Int} (h : arr.length ≥ 2) :
  let first := arr.get ⟨0, by exact Nat.zero_lt_of_lt h⟩
  let second := arr.get ⟨1, by exact h⟩
  max_turbulence_size [first, second] = if first = second then 1 else 2 :=
  sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval max_turbulence_size [9, 4, 2, 10, 7, 8, 8, 1, 9]

/-
info: 2
-/
-- #guard_msgs in
-- #eval max_turbulence_size [4, 8, 12, 16]

/-
info: 1
-/
-- #guard_msgs in
-- #eval max_turbulence_size [100]

-- Apps difficulty: interview
-- Assurance level: unguarded