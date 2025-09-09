-- <vc-helpers>
-- </vc-helpers>

def max_abs_sum_pairs (n : Nat) (arr : List Int) : Int :=
  sorry

-- Length of input array is even and at least 2

theorem max_abs_sum_pairs_input_valid (n : Nat) (arr : List Int) :
  n ≥ 2 → n % 2 = 0 → arr.length = n := by
  sorry

theorem max_abs_sum_pairs_non_negative (n : Nat) (arr : List Int) :
  max_abs_sum_pairs n arr ≥ 0 := by 
  sorry

theorem max_abs_sum_pairs_preserves_length (n : Nat) (arr : List Int) :
  arr.length = n := by
  sorry

theorem max_abs_sum_pairs_same_elements (n : Nat) (arr : List Int) :
  List.length arr = n := by
  sorry

theorem max_abs_sum_pairs_bounded (n : Nat) (arr : List Int) (bound : Int) : 
  (∀ x ∈ arr, -1000 ≤ x ∧ x ≤ 1000) →
  max_abs_sum_pairs n arr ≤ bound := by
  sorry

theorem max_abs_sum_pairs_achieves_maximum (n : Nat) (arr : List Int) (max : Int) :
  max_abs_sum_pairs n arr = max := by
  sorry

theorem max_abs_sum_pairs_zero_array (n : Nat) :
  n ≥ 2 → n % 2 = 0 →
  max_abs_sum_pairs n (List.replicate n 0) = 0 := by
  sorry

/-
info: 9
-/
-- #guard_msgs in
-- #eval max_abs_sum_pairs 4 [1, -3, 2, -3]

/-
info: 10
-/
-- #guard_msgs in
-- #eval max_abs_sum_pairs 2 [5, -5]

/-
info: 12
-/
-- #guard_msgs in
-- #eval max_abs_sum_pairs 6 [1, 2, 3, -1, -2, -3]

-- Apps difficulty: interview
-- Assurance level: unguarded