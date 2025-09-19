-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def odd_count (n : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem odd_count_nonnegative (n : Nat) :
  odd_count n ≥ 0 :=
  sorry

theorem odd_count_half_input (n : Nat) :
  odd_count n = n / 2 :=
  sorry

theorem odd_count_consecutive_diff (n : Nat) :
  odd_count (n + 1) - odd_count n ≤ 1 :=
  sorry
-- </vc-theorems>