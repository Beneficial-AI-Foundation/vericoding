-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def array_previous_less (arr : List Int) : List Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem array_previous_less_length (arr : List Int) (h : arr ≠ []) :
  (array_previous_less arr).length = arr.length :=
  sorry

theorem array_previous_less_values (arr : List Int) (h : arr ≠ []) (i : Nat) (hi : i < arr.length) :
  let result := array_previous_less arr
  if result[i]! ≠ -1 then
    (∃ j, j < i ∧ arr[j]! = result[i]! ∧ arr[j]! < arr[i]! ∧
      ∀ k, j < k → k < i → arr[k]! ≥ arr[i]!)
  else True :=
  sorry

theorem array_previous_less_negative_ones (arr : List Int) (h : arr ≠ []) (i : Nat) (hi : i < arr.length) :
  let result := array_previous_less arr
  if result[i]! = -1 then
    ∀ j, j < i → arr[j]! ≥ arr[i]!
  else True :=
  sorry

theorem array_previous_less_strictly_decreasing (arr : List Int) (h : arr ≠ []) 
  (h_positive : ∀ x ∈ arr, x > 0)
  (h_decreasing : ∀ i j, i < j → j < arr.length → arr[i]! > arr[j]!) :
  array_previous_less arr = List.replicate arr.length (-1) :=
  sorry
-- </vc-theorems>