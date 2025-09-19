-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def number_of_carries (a b : Nat) : Nat := sorry

theorem carries_non_negative (a b : Nat) : 
  number_of_carries a b ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem carries_max_digits (a b : Nat) :
  number_of_carries a b ≤ String.length (toString (max a b)) := sorry

theorem carries_with_zero (x : Nat) :
  number_of_carries x 0 = 0 ∧ number_of_carries 0 x = 0 := sorry

theorem single_digit_no_carry {d1 d2 : Nat} :
  d1 ≤ 9 → d2 ≤ 9 → d1 + d2 < 10 → 
  number_of_carries d1 d2 = 0 := sorry

theorem identical_numbers (x : Nat) :
  number_of_carries x x = number_of_carries x x := sorry
-- </vc-theorems>