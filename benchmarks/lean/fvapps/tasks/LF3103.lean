-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count (n : Int) : Int := sorry

theorem count_monotonic {n : Int} (h : n ≥ 5) : 
  count n ≥ count (n-1) := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem count_negative_input {n : Int} (h : n < 0) : 
  count n = sorry := sorry
-- </vc-theorems>