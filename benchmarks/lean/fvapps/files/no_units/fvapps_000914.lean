-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_even_sum_pairs (a b : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_even_sum_pairs_positive (a b : Nat) 
  (h1 : a > 0) (h2 : b > 0) (h3 : a ≤ 1000) (h4 : b ≤ 1000) : 
  count_even_sum_pairs a b ≥ 0 :=
sorry

theorem count_even_sum_pairs_symmetric (a b : Nat)
  (h1 : a > 0) (h2 : b > 0) (h3 : a ≤ 1000) (h4 : b ≤ 1000) :
  count_even_sum_pairs a b = count_even_sum_pairs b a :=
sorry

theorem count_even_sum_pairs_same_input (n : Nat)
  (h1 : n > 0) (h2 : n ≤ 1000) :
  count_even_sum_pairs n n ≥ n / 2 :=
sorry

theorem count_even_sum_pairs_small_inputs :
  count_even_sum_pairs 1 1 = 1 ∧ 
  count_even_sum_pairs 1 2 = 1 ∧ 
  count_even_sum_pairs 2 2 = 2 :=
sorry

theorem count_even_sum_pairs_bounds (a b : Nat)
  (h1 : a > 0) (h2 : b > 0) (h3 : a ≤ 1000) (h4 : b ≤ 1000) :
  count_even_sum_pairs a b ≤ a * b :=
sorry
-- </vc-theorems>