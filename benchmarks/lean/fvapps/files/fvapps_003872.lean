-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def performant_smallest (arr : List Int) (n : Nat) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem performant_smallest_length_eq_n {arr : List Int} {n : Nat} 
  (h : 0 < arr.length) (h2 : n ≤ arr.length) :
  (performant_smallest arr n).length = n :=
sorry

theorem performant_smallest_elements_from_arr {arr : List Int} {n : Nat} 
  (h : 0 < arr.length) (h2 : n ≤ arr.length) :
  ∀ x, x ∈ performant_smallest arr n → x ∈ arr :=
sorry

theorem performant_smallest_full_list {arr : List Int} (h : 0 < arr.length) :
  performant_smallest arr arr.length = arr :=
sorry
-- </vc-theorems>