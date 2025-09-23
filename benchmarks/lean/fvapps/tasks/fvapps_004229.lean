-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def adjacentElementProduct (arr : List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem adjacent_product_is_product_of_adjacent_elements {arr : List Int} 
  (h : arr.length ≥ 2) :
  ∃ (i : Nat), i + 1 < arr.length ∧ adjacentElementProduct arr = arr[i]! * arr[i+1]! :=
  sorry

theorem adjacent_product_is_maximum {arr : List Int} 
  (h : arr.length ≥ 2) :
  ∀ (i : Nat), i + 1 < arr.length → 
    adjacentElementProduct arr ≥ arr[i]! * arr[i+1]! :=
  sorry

theorem adjacent_product_commutative {arr : List Int}
  (h : arr.length ≥ 2) :
  adjacentElementProduct arr = adjacentElementProduct arr.reverse :=
  sorry

theorem adjacent_product_error_empty :
  ¬∃ (result : Int), adjacentElementProduct [] = result :=
  sorry

theorem adjacent_product_error_singleton (x : Int) :
  ¬∃ (result : Int), adjacentElementProduct [x] = result :=
  sorry
-- </vc-theorems>