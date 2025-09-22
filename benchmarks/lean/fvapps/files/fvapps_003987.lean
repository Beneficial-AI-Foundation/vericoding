-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def three_details (n : Nat) : Nat := sorry

-- Non-negativity theorem
-- </vc-definitions>

-- <vc-theorems>
theorem three_details_nonnegative (n : Nat) (h : n > 0) :
  three_details n ≥ 0 := sorry

-- Doubling monotonicity theorem

theorem three_details_doubling (n : Nat) (h : n > 0) :
  three_details (2 * n) ≥ three_details n := sorry

-- Periodic behavior theorem

theorem three_details_periodic (n : Nat) (h : n > 3) :
  three_details n = three_details (n / 2) + three_details (n / 2 + n % 2) := sorry

-- Base cases theorems

theorem three_details_base_one : three_details 1 = 0 := sorry

theorem three_details_base_two : three_details 2 = 0 := sorry

theorem three_details_base_three : three_details 3 = 1 := sorry
-- </vc-theorems>