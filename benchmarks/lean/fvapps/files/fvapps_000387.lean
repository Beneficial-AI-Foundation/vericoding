-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_digit_one (n : Nat) : Nat := sorry

def count_ones_brute_force (n : Nat) : Nat := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_digit_one_matches_brute_force (n : Nat) : 
  count_digit_one n = count_ones_brute_force n := sorry

theorem count_digit_one_boundary_values (n : Nat) (h : n = 0 ∨ n = 1 ∨ n = 9 ∨ n = 10 ∨ n = 11 ∨ n = 99 ∨ n = 100) :
  count_digit_one n = count_ones_brute_force n := sorry

theorem count_digit_one_monotonic (n : Nat) :
  count_digit_one n ≤ count_digit_one (n + 1) := sorry

theorem count_digit_one_nonnegative (n : Nat) :
  count_digit_one n ≥ 0 := sorry

theorem count_digit_one_zero :
  count_digit_one 0 = 0 := sorry
-- </vc-theorems>