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

/-
info: 6
-/
-- #guard_msgs in
-- #eval solve_sequence_split 6 [1, 2, 1, 1, 3, 1]

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve_sequence_split 3 [4, 1, 4]
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: unguarded