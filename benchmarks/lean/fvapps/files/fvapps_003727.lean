-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def digSum (n : Nat) (p : Nat) : Nat :=
  sorry

def digPow (n : Nat) (p : Nat) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem digPow_valid_result {n p : Nat} (h : digPow n p ≠ -1) :
  digSum n p = (digPow n p).toNat * n ∧ digPow n p > 0 := by
  sorry

theorem digPow_is_int (n p : Nat) :
  ∃ k : Int, digPow n p = k := by
  sorry

theorem digPow_power_one (n : Nat) :
  digSum n 1 % n = 0 →
  digPow n 1 = (digSum n 1) / n := by
  sorry

theorem digPow_power_one_neg (n : Nat) :
  digSum n 1 % n ≠ 0 →
  digPow n 1 = -1 := by
  sorry

theorem digPow_single_digit_power_one (n : Nat) :
  n > 0 → n < 10 →
  digPow n 1 = 1 := by
  sorry

theorem digPow_large_power_is_int (n p : Nat) :
  ∃ k : Int, digPow n p = k := by
  sorry
-- </vc-theorems>