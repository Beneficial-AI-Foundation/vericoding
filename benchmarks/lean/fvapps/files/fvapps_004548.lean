-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def equalize (arr : List Int) : List String := sorry

theorem equalize_format (arr : List Int) (h : arr.length > 0) :
  let result := equalize arr
  ∀ x ∈ result, ∃ s : String, (x = s) ∧ (s.get 0 = '+' ∨ s.get 0 = '-') := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem equalize_first_elem (arr : List Int) (h : arr.length > 0) :
  (equalize arr).head! = "+0" := sorry

theorem equalize_length (arr : List Int) (h : arr.length > 0) :
  (equalize arr).length = arr.length := sorry

theorem equalize_relative_diffs (arr : List Int) (h : arr.length > 0) :
  let result := equalize arr
  ∀ i, i < arr.length →
    String.toInt! (result.get! i) = arr.get! i - arr.get! 0 := sorry

theorem equalize_consecutive_diffs (arr : List Int) (h : arr.length > 0) :
  let result := equalize arr
  ∀ i, i < arr.length - 1 →
    String.toInt! (result.get! (i+1)) - String.toInt! (result.get! i) = 
    arr.get! (i+1) - arr.get! i := sorry
-- </vc-theorems>