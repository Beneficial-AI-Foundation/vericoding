/-
# Task
 Given array of integers, for each position i, search among the previous positions for the last (from the left) position that contains a smaller value. Store this value at position i in the answer. If no such value can be found, store `-1` instead.

# Example

 For `items = [3, 5, 2, 4, 5]`, the output should be `[-1, 3, -1, 2, 4]`.

# Input/Output

 - `[input]` integer array `arr`

   Non-empty array of positive integers.

   Constraints: `3 ≤ arr.length ≤ 1000, 1 ≤ arr[i] ≤ 1000.`

 - `[output]` an integer array

   Array containing answer values computed as described above.
-/

-- <vc-helpers>
-- </vc-helpers>

def array_previous_less (arr : List Int) : List Int :=
  sorry

theorem array_previous_less_length (arr : List Int) (h : arr ≠ []) :
  (array_previous_less arr).length = arr.length :=
  sorry

theorem array_previous_less_values (arr : List Int) (h : arr ≠ []) (i : Nat) (hi : i < arr.length) :
  let result := array_previous_less arr
  if result[i]! ≠ -1 then
    (∃ j, j < i ∧ arr[j]! = result[i]! ∧ arr[j]! < arr[i]! ∧
      ∀ k, j < k → k < i → arr[k]! ≥ arr[i]!)
  else True :=
  sorry

theorem array_previous_less_negative_ones (arr : List Int) (h : arr ≠ []) (i : Nat) (hi : i < arr.length) :
  let result := array_previous_less arr
  if result[i]! = -1 then
    ∀ j, j < i → arr[j]! ≥ arr[i]!
  else True :=
  sorry

theorem array_previous_less_strictly_decreasing (arr : List Int) (h : arr ≠ []) 
  (h_positive : ∀ x ∈ arr, x > 0)
  (h_decreasing : ∀ i j, i < j → j < arr.length → arr[i]! > arr[j]!) :
  array_previous_less arr = List.replicate arr.length (-1) :=
  sorry

/-
info: [-1, 3, -1, 2, 4]
-/
-- #guard_msgs in
-- #eval array_previous_less [3, 5, 2, 4, 5]

/-
info: [-1, -1, -1, 1, 3, 4, 4, 1]
-/
-- #guard_msgs in
-- #eval array_previous_less [2, 2, 1, 3, 4, 5, 5, 3]

/-
info: [-1, -1, -1]
-/
-- #guard_msgs in
-- #eval array_previous_less [3, 2, 1]

-- Apps difficulty: introductory
-- Assurance level: unguarded