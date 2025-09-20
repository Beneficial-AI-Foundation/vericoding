-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def compute_expected_score (n : Nat) (probs : List Float) : Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem score_is_nonnegative {n : Nat} {probs : List Float} 
  (h1 : ∀ p ∈ probs, 0 ≤ p ∧ p ≤ 1)
  (h2 : probs.length = n) :
  0 ≤ compute_expected_score n probs :=
sorry

theorem score_with_zero_probs {n : Nat} {probs : List Float}
  (h1 : probs.length = n) 
  (h2 : probs = List.replicate n 0) :
  compute_expected_score n probs = 0 :=
sorry

theorem score_monotonic_with_all_ones {n : Nat} {probs : List Float}
  (h1 : ∀ p ∈ probs, 0 ≤ p ∧ p ≤ 1)
  (h2 : probs.length = n) :
  compute_expected_score n probs ≤ compute_expected_score n (List.replicate n 1) :=
sorry

theorem length_matches_probability_list {n : Nat} {probs : List Float}
  (h1 : ∀ p ∈ probs, 0 ≤ p ∧ p ≤ 1)
  (h2 : probs.length = n)
  (h3 : n > 0) :
  ∃ score : Float, compute_expected_score n probs = score :=
sorry
-- </vc-theorems>