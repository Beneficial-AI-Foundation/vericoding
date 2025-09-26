-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_num (n : Nat) : Nat := sorry

theorem find_num_non_negative (n : Nat) (h : n > 0) :
  find_num n ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_num_unique {n : Nat} (h : n > 0) :
  ∀ i j, 1 ≤ i → i ≤ n → 1 ≤ j → j ≤ n → i ≠ j → find_num i ≠ find_num j := sorry

theorem find_num_upper_bound (n : Nat) (h : n > 0) :
  find_num n < 10000 := sorry
-- </vc-theorems>