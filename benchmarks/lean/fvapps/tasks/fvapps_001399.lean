-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def rearrange_array (n : Nat) (arr : List Int) : List Int := sorry

theorem rearrange_array_maintains_same_elements {n : Nat} {arr : List Int} 
  (h : arr.length > 0) :
  let result := rearrange_array n arr
  List.length result = n ∧ 
  List.length (List.filter (λ x => x ∈ result) arr) = List.length arr := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem rearrange_array_alternates {n : Nat} {arr : List Int}
  (h : arr.length > 1) :
  let result := rearrange_array n arr
  ∀ i, 1 ≤ i → i < n →
    (i % 2 = 0 → result[i]! ≥ result[i-1]!) ∧ 
    (i % 2 = 1 → result[i]! ≤ result[i-1]!) := sorry

theorem rearrange_array_idempotent {n : Nat} {arr : List Int}
  (h : arr.length > 0) :
  let result1 := rearrange_array n arr
  let result2 := rearrange_array n result1
  result1 = result2 := sorry
-- </vc-theorems>