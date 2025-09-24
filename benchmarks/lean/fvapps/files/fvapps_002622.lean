-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def multiple_of_index (arr : List Int) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem multiple_of_index_basic_properties (arr : List Int) (h : arr ≠ []) :
  let result := multiple_of_index arr
  -- Result length is at most one less than input length
  result.length ≤ arr.length - 1 ∧
  -- Every element in result appears in original array 
  ∀ x ∈ result, x ∈ arr :=
  sorry

theorem empty_result_divisibility (arr : List Int) (h : arr ≠ []) :
  let result := multiple_of_index arr
  (∀ (i : Fin arr.length), 1 ≤ i.val → (arr.get i) % i.val ≠ 0) →
  result = [] :=
  sorry

theorem all_zeros (arr : List Int) (h : arr.length ≥ 2) (h2 : ∀ x ∈ arr, x = 0) :
  let result := multiple_of_index arr
  (∀ x ∈ result, x = 0) ∧
  result.length = arr.length - 1 :=
  sorry
-- </vc-theorems>