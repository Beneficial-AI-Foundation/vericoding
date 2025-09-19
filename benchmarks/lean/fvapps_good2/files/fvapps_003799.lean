-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def reverse_bits (n : Nat) : Nat :=
sorry

def count_ones (n : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem reverse_bits_nonneg (n : Nat) :
  reverse_bits n ≥ 0 :=
sorry

theorem reverse_bits_preserves_ones (n : Nat) (h : n < 2^32) :
  count_ones n = count_ones (reverse_bits n) :=
sorry

theorem reverse_bits_preserves_power_of_two (n : Nat) (h : n < 2^32)
  (h₁ : n ≠ 0) (h₂ : n &&& (n - 1) = 0) :
  (reverse_bits n) &&& ((reverse_bits n) - 1) = 0 :=
sorry

theorem reverse_bits_zero :
  reverse_bits 0 = 0 :=
sorry

theorem reverse_bits_one :
  reverse_bits 1 = 1 :=
sorry
-- </vc-theorems>