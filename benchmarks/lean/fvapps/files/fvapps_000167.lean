-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_length_of_shortest_subarray (arr : List Int) : Nat :=
  sorry

def isNonDecreasing (l : List Int) : Bool :=
  sorry

def removeSubarray (arr : List Int) (start : Nat) (len : Nat) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem output_bounds (arr : List Int) :
  let result := find_length_of_shortest_subarray arr
  0 ≤ result ∧ result ≤ arr.length :=
sorry

theorem valid_removal_exists (arr : List Int) (h : arr ≠ []) :
  let result := find_length_of_shortest_subarray arr
  ∃ i : Nat, i + result ≤ arr.length ∧
    isNonDecreasing (removeSubarray arr i result) :=
sorry

theorem cannot_remove_fewer (arr : List Int) (h : arr ≠ []) :
  let result := find_length_of_shortest_subarray arr
  result = 0 → isNonDecreasing arr
  ∧
  result > 0 → ∀ i : Nat, i + (result - 1) ≤ arr.length →
    ¬isNonDecreasing (removeSubarray arr i (result - 1)) :=
sorry

theorem sorted_returns_zero (arr : List Int) (h : arr ≠ []) :
  isNonDecreasing arr → find_length_of_shortest_subarray arr = 0 :=
sorry

theorem small_arrays (arr : List Int) :
  arr.length ≤ 1 → find_length_of_shortest_subarray arr = 0
  ∧
  (arr.length = 2 →
    find_length_of_shortest_subarray arr =
      if arr.get! 0 ≤ arr.get! 1 then 0 else 1) :=
sorry
-- </vc-theorems>