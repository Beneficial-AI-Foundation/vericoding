-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def rec (n : Int) : Int := sorry

theorem rec_non_negative (n : Int) : n ≥ 0 → rec n ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem rec_zero_or_negative (n : Int) : n ≤ 0 → rec n = 0 := sorry

theorem rec_strictly_increasing (n : Int) : n > 1 → rec n > rec (n-1) := sorry

theorem rec_grows_linearly (n : Int) : n > 1 → rec n ≥ n-1 := sorry
-- </vc-theorems>