-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_transition_point (n : Nat) (arr : List Nat) : Option Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_transition_point_valid_index (n : Nat) (arr : List Nat) :
  let result := find_transition_point n arr
  ∀ i, result = some i → i < n := 
  sorry

theorem find_transition_point_zeros_before (n : Nat) (arr : List Nat) :
  let result := find_transition_point n arr
  ∀ i, result = some i →
  ∀ j < i, arr[j]! = 0 := 
  sorry

theorem find_transition_point_first_one (n : Nat) (arr : List Nat) :
  let result := find_transition_point n arr
  ∀ i, result = some i →
  i < n →
  arr[i]! = 1 :=
  sorry

theorem find_transition_point_no_ones (n : Nat) (arr : List Nat) :
  (∀ x ∈ arr, x ≠ 1) →
  find_transition_point n arr = none :=
  sorry

theorem find_transition_point_all_ones (n : Nat) :
  n > 0 →
  find_transition_point n (List.replicate n 1) = some 0 :=
  sorry

theorem find_transition_point_all_zeros (n : Nat) :
  n > 0 →
  find_transition_point n (List.replicate n 0) = none :=
  sorry
-- </vc-theorems>