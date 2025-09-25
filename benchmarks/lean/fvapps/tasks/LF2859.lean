-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def consecutive_sum (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_is_positive (n : Nat) (h : n > 0) : consecutive_sum n ≥ 0 :=
  sorry

theorem min_representation (n : Nat) (h : n > 0) : consecutive_sum n ≥ 1 :=
  sorry

theorem result_less_than_input (n : Nat) (h : n > 0) : consecutive_sum n ≤ n :=
  sorry
-- </vc-theorems>