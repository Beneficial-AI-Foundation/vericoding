-- <vc-helpers>
-- </vc-helpers>

def count_triplets (arr: List Nat) : Nat :=
  sorry

theorem count_triplets_non_negative (arr: List Nat) :
  count_triplets arr ≥ 0 :=
sorry

theorem count_triplets_is_nat (arr: List Nat) :
  count_triplets arr = count_triplets arr :=
sorry

theorem count_triplets_append_zero (arr: List Nat) :
  count_triplets (arr ++ [0]) ≥ count_triplets arr :=
sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval count_triplets [2, 3, 1, 6, 7]

/-
info: 10
-/
-- #guard_msgs in
-- #eval count_triplets [1, 1, 1, 1, 1]

/-
info: 3
-/
-- #guard_msgs in
-- #eval count_triplets [1, 3, 5, 7, 9]

-- Apps difficulty: interview
-- Assurance level: unguarded