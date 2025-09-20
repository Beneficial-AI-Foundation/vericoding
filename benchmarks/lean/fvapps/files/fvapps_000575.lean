-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def sumDigits (n : Nat) : Nat := sorry

def find_jojo_aadhar (n : Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem digit_sum_div_ten (n : Nat) : 
  (sumDigits (find_jojo_aadhar n)) % 10 = 0 := sorry

theorem matches_input_except_last (n : Nat) :
  find_jojo_aadhar n / 10 = n := sorry

theorem last_digit_in_range (n : Nat) :
  0 ≤ find_jojo_aadhar n % 10 ∧ find_jojo_aadhar n % 10 ≤ 9 := sorry
-- </vc-theorems>