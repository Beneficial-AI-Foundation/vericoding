-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def arrange_array (n : Nat) (arr : List Nat) : List Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem arrange_array_valid {n : Nat} {arr : List Nat} (h1 : 0 < n) :
  let result := arrange_array n arr
  -- Output length is n
  List.length result = n ∧ 
  -- All elements are non-negative and less than n
  (∀ x ∈ result, 0 ≤ x ∧ x < n) ∧
  -- All non-zero elements in result came from input array
  (∀ x ∈ result, x ≠ 0 → x ∈ arr) ∧
  -- All valid elements from input array appear in result
  (∀ x ∈ arr, x < n → x ∈ result) :=
  sorry

theorem arrange_array_empty {n : Nat} (h1 : 0 < n) :
  arrange_array n [] = List.replicate n 0 :=
  sorry

theorem arrange_array_negative {n : Nat} {arr : List Int} 
  (h1 : 0 < n)
  (h2 : ∀ x ∈ arr, x < 0) :
  arrange_array n (arr.map Int.toNat) = List.replicate n 0 :=
  sorry

theorem arrange_array_too_large {n : Nat} {arr : List Nat}
  (h1 : 0 < n)
  (h2 : ∀ x ∈ arr, n ≤ x) :
  ∀ x ∈ arrange_array n arr, x = 0 :=
  sorry
-- </vc-theorems>