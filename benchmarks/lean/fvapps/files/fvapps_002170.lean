-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_haiku_sequences (n k1 k2 k3 : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem small_n_property (n : Nat) (h : 1 ≤ n ∧ n ≤ 3) :
  count_haiku_sequences n 2 2 2 < 10^n := sorry

theorem edge_case_min_inputs :
  count_haiku_sequences 1 1 1 1 ≥ 0 := sorry

theorem edge_case_small_inputs :
  count_haiku_sequences 2 2 2 2 < 10^2 := sorry

theorem original_test_case_1 :
  count_haiku_sequences 3 5 7 5 = 1 := sorry

theorem original_test_case_2 :  
  count_haiku_sequences 4 5 7 5 = 34 := sorry
-- </vc-theorems>