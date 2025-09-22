-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def somethingAcci (num_digits: Nat) : Nat × Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem sequence_length_at_least_six (n: Nat) : (somethingAcci n).1 ≥ 6 :=
  sorry

theorem final_digit_length_meets_request (n: Nat) : (somethingAcci n).2 ≥ n :=
  sorry

theorem sequence_grows_monotonically {n: Nat} (h: n > 1) : 
  (somethingAcci n).1 ≥ (somethingAcci (n-1)).1 ∧ 
  (somethingAcci n).2 ≥ (somethingAcci (n-1)).2 :=
  sorry
-- </vc-theorems>