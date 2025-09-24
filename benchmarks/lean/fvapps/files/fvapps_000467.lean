-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_kth_bit (n : Nat) (k : Nat) : Char := 
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_kth_bit_valid_output (n : Nat) (k : Nat) (h1 : n > 0) (h2 : k > 0) (h3 : k ≤ 2^n - 1) : 
  find_kth_bit n k = '0' ∨ find_kth_bit n k = '1' := sorry

theorem find_kth_bit_first_is_zero (n : Nat) (h : n > 0) :
  find_kth_bit n 1 = '0' := sorry

theorem find_kth_bit_middle_is_one (n : Nat) (h : n > 1) :
  find_kth_bit n ((2^n - 1)/2 + 1) = '1' := sorry

theorem find_kth_bit_specific_cases :
  find_kth_bit 3 1 = '0' ∧ 
  find_kth_bit 4 11 = '1' ∧
  find_kth_bit 1 1 = '0' := sorry
-- </vc-theorems>