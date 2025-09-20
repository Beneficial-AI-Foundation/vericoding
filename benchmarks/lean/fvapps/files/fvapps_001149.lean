-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_sequence_split (N: Nat) (seq: List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sequence_split_nonneg (N: Nat) (seq: List Nat) :
  (N ≥ 2) →
  (∀ x ∈ seq, x ≤ 100) →
  solve_sequence_split N seq ≥ 0 :=
sorry

theorem sequence_split_upper_bound (N: Nat) (seq: List Nat) :
  (N ≥ 2) → 
  (∀ x ∈ seq, x ≤ 100) →
  solve_sequence_split N seq ≤ N * (N - 1) :=
sorry

theorem sequence_split_all_zeros (N: Nat) (seq: List Nat) :
  (N ≥ 2) →
  (∀ x ∈ seq, x = 0) →
  solve_sequence_split N seq = N * (N - 1) :=
sorry

theorem sequence_split_symmetry (N: Nat) (seq: List Nat) :
  (N ≥ 2) →
  (∀ x ∈ seq, x ≥ 1) →
  (∀ x ∈ seq, x ≤ 100) →
  solve_sequence_split N seq = solve_sequence_split N seq.reverse :=
sorry
-- </vc-theorems>