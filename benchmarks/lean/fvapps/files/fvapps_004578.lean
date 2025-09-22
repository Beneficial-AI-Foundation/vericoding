-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def simpson (n : Nat) : Float := sorry

def Even (n : Nat) : Prop := ∃ k, n = 2 * k

-- Property: Result should converge to 2.0 for increasing n
-- </vc-definitions>

-- <vc-theorems>
theorem simpson_convergence {n : Nat} (h : n ≥ 10) : 
  (simpson n - 2).abs ≤ 0.001 := sorry

-- Property: Even n should give more accurate results than n-1 

theorem even_more_accurate {n : Nat} (h1 : n ≥ 20) (h2 : Even n) :
  (simpson n - 2).abs ≤ (simpson (n-1) - 2).abs := sorry

-- Property: Larger n should give more accurate results

theorem accuracy_improves {n : Nat} (h : n ≥ 10) :
  (simpson (2*n) - 2).abs ≤ (simpson n - 2).abs := sorry

-- Property: Result should be positive

theorem positive_result {n : Nat} (h : n ≥ 10) :
  simpson n > 0 := sorry

-- Property: Small n should still give reasonable results

theorem small_n_reasonable :
  1.9 ≤ simpson 10 ∧ simpson 10 ≤ 2.1 := sorry
-- </vc-theorems>