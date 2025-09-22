-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def digits (n : Nat) : List Nat := sorry 

def special_number (n : Nat) : String := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem special_number_output_valid (n : Nat) :
  special_number n = "Special!!" ∨ special_number n = "NOT!!" := sorry

theorem special_number_iff_digits_le_five (n : Nat) :
  (∀ d, d ∈ digits n → d ≤ 5) ↔ special_number n = "Special!!" := sorry

theorem special_number_when_digits_le_five (n : Nat) :
  (∀ d, d ∈ digits n → d ≤ 5) → special_number n = "Special!!" := sorry

theorem non_special_number_when_digit_gt_five (n : Nat) :
  (∃ d, d ∈ digits n ∧ d > 5) → special_number n = "NOT!!" := sorry
-- </vc-theorems>