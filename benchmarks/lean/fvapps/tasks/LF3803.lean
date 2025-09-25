-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def digits_average (n : Nat) : Nat := sorry

theorem digits_average_result_in_range (n : Nat) (h : n > 0) : 
  digits_average n ≤ 9 ∧ digits_average n ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_digit_unchanged (n : Nat) (h1 : n > 0) (h2 : n ≤ 9) :
  digits_average n = n := sorry
-- </vc-theorems>