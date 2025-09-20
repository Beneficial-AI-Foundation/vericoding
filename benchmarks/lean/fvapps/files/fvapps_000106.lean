-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_array_sharpenable (n : Nat) (arr : List Int) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem array_len_matches_param {n : Nat} {arr : List Int} 
  (h1 : arr.length > 0) :
  is_array_sharpenable n arr = is_array_sharpenable arr.length arr :=
sorry

theorem negative_values_work {n : Nat} {arr : List Int}
  (h1 : arr.length > 0) :
  ∃ result : Bool, is_array_sharpenable n arr = result :=
sorry

theorem strictly_decreasing_large_numbers {n : Nat} {arr : List Int}
  (h1 : arr.length > 0)
  (h2 : ∀ x ∈ arr, x > 0)
  (h3 : ∀ x ∈ arr, ∃ y : Int, y = x * n)
  (h4 : ∀ (i j : Fin arr.length), i < j → arr.get i > arr.get j) :
  is_array_sharpenable n arr = true :=
sorry

theorem all_zeros_not_sharpenable {n : Nat} {arr : List Int}
  (h1 : n > 1)
  (h2 : arr = List.replicate n 0) :
  is_array_sharpenable n arr = false :=
sorry
-- </vc-theorems>