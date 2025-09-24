-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sort_array (arr : List Int) : List Int := sorry

theorem sort_array_preserves_length {arr : List Int} : 
  (sort_array arr).length = arr.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sort_array_preserves_elements {arr : List Int} :
  ∀ x, (List.count x arr) = (List.count x (sort_array arr)) := sorry

theorem sort_array_empty :
  sort_array [] = [] := sorry
-- </vc-theorems>