-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sort_by_value_and_index (arr : List Int) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sort_by_value_and_index_preserves_elements {arr : List Int} (h : arr ≠ []) :
  List.Perm (sort_by_value_and_index arr) arr :=
sorry

theorem sort_by_value_and_index_length {arr : List Int} (h : arr ≠ []) :
  (sort_by_value_and_index arr).length = arr.length :=
sorry
-- </vc-theorems>