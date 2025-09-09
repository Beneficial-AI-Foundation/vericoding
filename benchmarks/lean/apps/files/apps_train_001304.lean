-- <vc-helpers>
-- </vc-helpers>

def arrange_array (n : Nat) (arr : List Nat) : List Nat :=
  sorry

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

/-
info: [0, 1]
-/
-- #guard_msgs in
-- #eval arrange_array 2 [1, 1]

/-
info: [0, 1, 2, 0]
-/
-- #guard_msgs in
-- #eval arrange_array 4 [1, 1, 2, 1]

/-
info: [0, 1, 2, 3, 4]
-/
-- #guard_msgs in
-- #eval arrange_array 5 [1, 2, 3, 4, 2]

-- Apps difficulty: interview
-- Assurance level: unguarded