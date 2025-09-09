def find_length_of_shortest_subarray (arr : List Int) : Nat :=
  sorry

def isNonDecreasing (l : List Int) : Bool :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def removeSubarray (arr : List Int) (start : Nat) (len : Nat) : List Int :=
  sorry

-- Output is between 0 and length of array

theorem output_bounds (arr : List Int) :
  let result := find_length_of_shortest_subarray arr
  0 ≤ result ∧ result ≤ arr.length :=
  sorry

-- There exists some subarray of length result that when removed makes array non-decreasing

theorem valid_removal_exists (arr : List Int) (h : arr ≠ []) :
  let result := find_length_of_shortest_subarray arr
  ∃ i : Nat, i + result ≤ arr.length ∧ 
    isNonDecreasing (removeSubarray arr i result) :=
  sorry

-- Cannot remove fewer elements to make array non-decreasing

theorem cannot_remove_fewer (arr : List Int) (h : arr ≠ []) :
  let result := find_length_of_shortest_subarray arr
  result = 0 → isNonDecreasing arr
  ∧
  result > 0 → ∀ i : Nat, i + (result - 1) ≤ arr.length →
    ¬isNonDecreasing (removeSubarray arr i (result - 1)) :=
  sorry

-- Sorted array returns 0

theorem sorted_returns_zero (arr : List Int) (h : arr ≠ []) :
  isNonDecreasing arr → find_length_of_shortest_subarray arr = 0 :=
  sorry

-- Small arrays

theorem small_arrays (arr : List Int) :
  arr.length ≤ 1 → find_length_of_shortest_subarray arr = 0
  ∧
  (arr.length = 2 → 
    find_length_of_shortest_subarray arr = 
      if arr.get! 0 ≤ arr.get! 1 then 0 else 1) :=
  sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval find_length_of_shortest_subarray [1, 2, 3, 10, 4, 2, 3, 5]

/-
info: 4
-/
-- #guard_msgs in
-- #eval find_length_of_shortest_subarray [5, 4, 3, 2, 1]

/-
info: 0
-/
-- #guard_msgs in
-- #eval find_length_of_shortest_subarray [1, 2, 3]

-- Apps difficulty: interview
-- Assurance level: unguarded