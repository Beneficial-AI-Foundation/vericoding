-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_smallest_int (arr : List Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_smallest_int_membership 
  (arr : List Int)
  (h : arr ≠ []) :
  find_smallest_int arr ∈ arr :=
sorry

theorem find_smallest_int_is_minimum
  (arr : List Int)
  (h : arr ≠ []) :
  ∀ x ∈ arr, find_smallest_int arr ≤ x :=
sorry
-- </vc-theorems>