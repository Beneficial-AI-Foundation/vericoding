-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def increasing_numbers (n : Nat) : Nat := sorry

theorem increasing_numbers_positive (n : Nat) : increasing_numbers n > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem increasing_numbers_monotonic (n : Nat) : 
  n > 0 → increasing_numbers n > increasing_numbers (n-1) := sorry

theorem increasing_numbers_base_cases : 
  increasing_numbers 0 = 1 ∧ 
  increasing_numbers 1 = 10 ∧ 
  increasing_numbers 2 = 55 := sorry
-- </vc-theorems>