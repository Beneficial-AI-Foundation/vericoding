-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def power_of_two (n : Nat) : Bool := sorry

theorem power_of_two_positive (n : Nat) :
  power_of_two n = true → n > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem power_of_two_div_two (n : Nat) :
  power_of_two n = true →
  ∃ k, n = 2^k := sorry

theorem power_of_two_single_bit (n : Nat) :
  power_of_two n = true →
  ∃ k, (n = 2^k ∧ ∀ m, n = 2^m → m = k) := sorry

theorem power_of_two_bitwise (n : Nat) :
  n > 0 →
  power_of_two n = true ↔ n &&& (n - 1) = 0 := sorry

theorem power_of_two_zero :
  power_of_two 0 = false := sorry
-- </vc-theorems>