-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_requests_to_add (n : Nat) (arr : List Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_element_no_changes (n : Nat) (h : n > 0) :
  min_requests_to_add 1 [n] = 0 :=
sorry

theorem sorted_array_no_changes {n : Nat} {arr : List Nat} 
  (h1 : arr.length = n)
  (h2 : n ≥ 2)
  (h3 : ∀ i j, i < j → j < arr.length → arr[i]! < arr[j]!) :
  min_requests_to_add n arr = 0 :=
sorry

theorem result_non_negative {n : Nat} {arr : List Nat}
  (h1 : arr.length = n)
  (h2 : n ≥ 2) :
  min_requests_to_add n arr ≥ 0 :=
sorry

theorem array_length_matches_n {n : Nat} {arr : List Nat}
  (h : arr.length = n) :
  min_requests_to_add n arr = min_requests_to_add (arr.length) arr :=
sorry

theorem array_length_error {n : Nat} {arr : List Nat}
  (h : arr.length < n) :
  min_requests_to_add n arr = min_requests_to_add arr.length arr :=
sorry
-- </vc-theorems>