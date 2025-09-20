-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def min_bandwidth (n : Nat) (matrix : List (List Nat)) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>