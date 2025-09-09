-- <vc-helpers>
-- </vc-helpers>

def count_binary_sequences (n : Nat) : Nat :=
sorry

theorem count_binary_sequences_modulo_bounds (n : Nat) (h : n ≥ 1) :
  count_binary_sequences n < 15746 :=
sorry

theorem count_binary_sequences_nonneg (n : Nat) :
  count_binary_sequences n ≥ 0 :=
sorry

theorem count_binary_sequences_base_cases :
  count_binary_sequences 1 = 1 ∧ count_binary_sequences 2 = 2 :=
sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval count_binary_sequences 4

/-
info: 1
-/
-- #guard_msgs in
-- #eval count_binary_sequences 1

/-
info: 2
-/
-- #guard_msgs in
-- #eval count_binary_sequences 2

-- Apps difficulty: interview
-- Assurance level: unguarded