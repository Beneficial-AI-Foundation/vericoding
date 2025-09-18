-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def arr_check (arr : List α) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem valid_array_of_arrays {α : Type} (arr : List (List α)) :
  arr_check arr = true :=
sorry

theorem invalid_array_of_non_arrays {α : Type} (arr : List α) 
  (h : arr.length ≥ 1) :
  arr_check arr = false :=
sorry

theorem array_of_empty_lists {α : Type} (arr : List (List α))
  (h : ∀ l ∈ arr, l.length = 0) :  
  arr_check arr = true :=
sorry
-- </vc-theorems>