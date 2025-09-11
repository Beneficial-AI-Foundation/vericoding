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

/-
info: 6
-/
-- #guard_msgs in
-- #eval adjacent_element_product [1, 2, 3]

/-
info: 50
-/
-- #guard_msgs in
-- #eval adjacent_element_product [9, 5, 10, 2, 24, -1, -48]

/-
info: -14
-/
-- #guard_msgs in
-- #eval adjacent_element_product [-23, 4, -5, 99, -27, 329, -2, 7, -921]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded