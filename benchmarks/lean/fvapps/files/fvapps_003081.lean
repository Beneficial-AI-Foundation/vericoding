-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def minimum (l : List Int) : Option Int :=
sorry

def maximum (l : List Int) : Option Int :=
sorry

def maximum_product (arr : List Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem maximum_product_in_array (arr : List Int) (h : arr ≠ []) :
  ∃ x ∈ arr, maximum_product arr = x :=
sorry

theorem maximum_product_even_negatives (arr : List Int) (h : arr ≠ [])
  (h_even : (arr.filter (λ x => x < 0)).length % 2 = 0) :
  let pos := arr.filter (λ x => x ≥ 0)
  let neg := arr.filter (λ x => x < 0)
  pos ≠ [] → (∃ m, minimum pos = some m ∧ maximum_product arr = m) ∨
  pos = [] → (∃ m, minimum neg = some m ∧ maximum_product arr = m) :=
sorry

theorem maximum_product_odd_negatives (arr : List Int) (h : arr ≠ [])
  (h_odd : (arr.filter (λ x => x < 0)).length % 2 = 1) :
  let neg := arr.filter (λ x => x < 0)
  (¬ arr.contains 0 → (∃ m, maximum neg = some m ∧ maximum_product arr = m)) ∧
  (arr.contains 0 → (∃ m, minimum neg = some m ∧ maximum_product arr = m)) :=
sorry

theorem maximum_product_multiple_zeros (arr : List Int) (h : arr ≠ [])
  (h_zeros : (arr.filter (λ x => x = 0)).length > 1) :
  ∃ m, minimum arr = some m ∧ maximum_product arr = m :=
sorry

theorem maximum_product_single_element (x : Int) :
  maximum_product [x] = x :=
sorry
-- </vc-theorems>