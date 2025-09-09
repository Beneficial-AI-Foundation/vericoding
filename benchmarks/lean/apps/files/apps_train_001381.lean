-- <vc-helpers>
-- </vc-helpers>

def min_bandwidth (n : Nat) (matrix : List (List Nat)) : Nat :=
  sorry

theorem bandwidth_bounds {n : Nat} {matrix : List (List Nat)} :
  n > 0 → min_bandwidth n matrix ≥ 0 ∧ min_bandwidth n matrix < n :=
  sorry

theorem zero_matrix_bandwidth {n : Nat} (matrix : List (List Nat)) :
  n > 0 →
  (∀ i j, i < n ∧ j < n → List.get! (List.get! matrix i) j = 0) →
  min_bandwidth n matrix = 0 :=
  sorry

theorem identity_matrix_bandwidth {n : Nat} (matrix : List (List Nat)) :
  n > 0 →
  (∀ i j, i < n ∧ j < n → List.get! (List.get! matrix i) j = if i = j then 1 else 0) →
  min_bandwidth n matrix = 0 :=
  sorry

theorem all_ones_matrix_bandwidth {n : Nat} (matrix : List (List Nat)) :
  n > 0 →
  (∀ i j, i < n ∧ j < n → List.get! (List.get! matrix i) j = 1) →
  min_bandwidth n matrix = n - 1 :=
  sorry

theorem bandwidth_monotonicity {n : Nat} {matrix₁ matrix₂ : List (List Nat)} :
  n > 0 →
  (∀ i j, i < n ∧ j < n → List.get! (List.get! matrix₁ i) j ≤ List.get! (List.get! matrix₂ i) j) →
  min_bandwidth n matrix₁ ≤ min_bandwidth n matrix₂ :=
  sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_bandwidth 2 [[0, 0], [0, 0]]

/-
info: 0
-/
-- #guard_msgs in
-- #eval min_bandwidth 2 [[1, 0], [0, 1]]

/-
info: 1
-/
-- #guard_msgs in
-- #eval min_bandwidth 3 [[1, 0, 0], [0, 1, 1], [1, 1, 0]]

/-
info: 3
-/
-- #guard_msgs in
-- #eval min_bandwidth 4 [[1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1]]

-- Apps difficulty: interview
-- Assurance level: guarded