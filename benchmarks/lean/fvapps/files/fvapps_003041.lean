-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def thirt (n : Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem thirt_stationary (n : Int) : n > 0 → thirt (thirt n) = thirt n :=
  sorry

theorem thirt_nonnegative (n : Int) : n > 0 → thirt n ≥ 0 :=
  sorry

theorem thirt_decreases_large_nums (n : Int) : n > 1000 → thirt n < n :=
  sorry

theorem thirt_deterministic (n : Int) : n > 0 → n ≤ 100 → thirt n = thirt n :=
  sorry

theorem thirt_nonzero_for_small (n : Int) : n > 0 → n ≤ 100 → thirt n > 0 :=
  sorry
-- </vc-theorems>