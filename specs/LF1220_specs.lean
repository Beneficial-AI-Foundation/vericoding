-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_sum_of_powers (N : Nat) (K : Nat) : Nat :=
  sorry

-- Basic properties
-- </vc-definitions>

-- <vc-theorems>
theorem count_sum_of_powers_non_negative (N K : Nat) : 
  count_sum_of_powers N K ≥ 0 :=
  sorry

theorem count_sum_of_powers_zero_for_small_N (N K : Nat) (h1 : K > 0) (h2 : N > 0) (h3 : N < 1^K) :
  count_sum_of_powers N K = 0 :=
  sorry

theorem count_sum_of_powers_zero_case (K : Nat) :
  count_sum_of_powers 0 K = 1 :=
  sorry

-- Square sums properties

theorem count_sum_squares_zero_for_impossible (N : Nat) 
  (h : N = 2 ∨ N = 3 ∨ N = 6 ∨ N = 7 ∨ N = 8 ∨ N = 11 ∨ N = 12 ∨ N = 15) :
  count_sum_of_powers N 2 = 0 :=
  sorry

theorem count_sum_squares_perfect_square (N : Nat) (h : ∃ k, N = k * k) :
  count_sum_of_powers N 2 ≥ 1 :=
  sorry

-- Small input properties

theorem count_sum_powers_small_N (N K : Nat) (h : N < 2^K) :
  count_sum_of_powers N K ≤ 1 :=
  sorry

theorem count_sum_powers_one_first_power :
  count_sum_of_powers 1 1 = 1 :=
  sorry
-- </vc-theorems>