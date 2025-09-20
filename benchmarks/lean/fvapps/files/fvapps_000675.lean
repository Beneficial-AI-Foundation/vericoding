-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_audience_meetings (days x y z : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem identical_periods
  (days period : Nat)
  (h1 : 1 ≤ days) (h2 : days ≤ 100)
  (h3 : 1 ≤ period) (h4 : period ≤ 100) :
  calculate_audience_meetings days period period period = (days * 24) / period :=
  sorry

theorem one_very_large_period
  (days x : Nat)
  (h1 : 1 ≤ days) (h2 : days ≤ 100)
  (h3 : 1 ≤ x) (h4 : x ≤ 100) :
  calculate_audience_meetings days x x 1000000000 = 0 :=
  sorry
-- </vc-theorems>