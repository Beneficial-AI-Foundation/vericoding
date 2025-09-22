-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_max_subarray (arr : List Int) : List Int :=
sorry

def sum_list (l : List Int) : Int :=
sorry

def all_subarrays_bounded_by_negatives (arr : List Int) : List (List Int) :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem all_positive_returns_full_array {arr : List Int}
  (h : ∀ x ∈ arr, x ≥ 0) (nonempty : arr ≠ []) :
  find_max_subarray arr = arr :=
sorry

theorem sum_is_maximal {arr : List Int} (nonempty : arr ≠ []) :
  let result := find_max_subarray arr
  let result_sum := sum_list result
  ∀ subarray ∈ all_subarrays_bounded_by_negatives arr,
    sum_list subarray ≤ result_sum :=
sorry
-- </vc-theorems>