-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_missing_numbers (arr : List Int) : List Int := sorry

theorem empty_or_single_returns_empty (arr : List Int) : 
  arr.length ≤ 1 → find_missing_numbers arr = [] := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem no_originals_in_result {arr : List Int} (h : arr.Nodup) :
  ∀ x ∈ find_missing_numbers arr, x ∉ arr := sorry

theorem result_is_sorted (arr : List Int) :
  ∀ i j, i < j → 
  i < (find_missing_numbers arr).length →
  j < (find_missing_numbers arr).length →
  (find_missing_numbers arr)[i]! ≤ (find_missing_numbers arr)[j]! := sorry
-- </vc-theorems>