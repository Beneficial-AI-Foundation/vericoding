-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_binary_sequences (n : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_binary_sequences_modulo_bounds (n : Nat) (h : n ≥ 1) :
  count_binary_sequences n < 15746 :=
sorry

theorem count_binary_sequences_nonneg (n : Nat) :
  count_binary_sequences n ≥ 0 :=
sorry

theorem count_binary_sequences_base_cases :
  count_binary_sequences 1 = 1 ∧ count_binary_sequences 2 = 2 :=
sorry
-- </vc-theorems>