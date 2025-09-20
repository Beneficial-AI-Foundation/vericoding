-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_nondecreasing_subarrays (arr : List Int) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem always_returns_positive {arr : List Int} (h : arr ≠ []) : 
  count_nondecreasing_subarrays arr > 0 :=
sorry

theorem single_element_returns_one {arr : List Int} (h : arr.length = 1) :
  count_nondecreasing_subarrays arr = 1 :=
sorry

theorem count_at_least_length {arr : List Int} (h : arr.length ≥ 2) :
  count_nondecreasing_subarrays arr ≥ arr.length :=
sorry
-- </vc-theorems>