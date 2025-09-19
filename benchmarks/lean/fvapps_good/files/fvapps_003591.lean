-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sort_transform (arr : List Int) : String := sorry

theorem sort_transform_output_length 
  {arr : List Int}
  (h1 : arr.length ≥ 4)
  (h2 : arr.length ≤ 20) 
  (h3 : ∀ x ∈ arr, x ≥ 33 ∧ x ≤ 126)
  (h4 : arr.Nodup) :
  (sort_transform arr).length = 19 := sorry
-- </vc-definitions>

-- <vc-theorems>
-- </vc-theorems>