-- <vc-preamble>
def abs (x : Int) : Int :=
  if x ≥ 0 then x else -x
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_distance_value (arr1 arr2 : List Int) (d : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_distance_value_non_negative
  (arr1 arr2 : List Int) (d : Nat)
  (h1 : arr1 ≠ []) (h2 : arr2 ≠ []) :
  find_distance_value arr1 arr2 d ≥ 0 :=
sorry

theorem find_distance_value_bounded
  (arr1 arr2 : List Int) (d : Nat)
  (h1 : arr1 ≠ []) (h2 : arr2 ≠ []) :
  find_distance_value arr1 arr2 d ≤ arr1.length :=
sorry

theorem find_distance_value_empty_arr2
  (arr1 : List Int) (d : Nat)
  (h : arr1 ≠ []) :
  find_distance_value arr1 [] d = arr1.length :=
sorry

theorem find_distance_value_zero_distance
  (arr1 arr2 : List Int)
  (h1 : arr1 ≠ []) (h2 : arr2 ≠ []) :
  find_distance_value arr1 arr2 0 =
    (arr1.filter (fun x => x ∉ arr2)).length :=
sorry
-- </vc-theorems>