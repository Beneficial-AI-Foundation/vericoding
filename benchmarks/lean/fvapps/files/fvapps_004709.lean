-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def temps (v0 d_tot : Float) (slope : Float) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem temps_returns_valid_output (v0 d_tot : Float) (slope : Float)
  (h1 : 3.1 ≤ v0 ∧ v0 ≤ 100)
  (h2 : -30 ≤ slope ∧ slope ≤ 30)
  (h3 : 0.1 ≤ d_tot ∧ d_tot ≤ 1000) :
  let result := temps v0 slope d_tot
  result ≥ -1 := by sorry

theorem steeper_slope_takes_longer (v0 d_tot : Float) (slope : Float)
  (h1 : 3.1 ≤ v0 ∧ v0 ≤ 100)
  (h2 : -30 ≤ slope ∧ slope ≤ 30)
  (h3 : 0.1 ≤ d_tot ∧ d_tot ≤ 1000)
  (h4 : slope ≥ 0)
  (h5 : temps v0 slope d_tot ≠ -1)
  (h6 : temps v0 (slope + 5) d_tot ≠ -1) :
  temps v0 (slope + 5) d_tot ≥ temps v0 slope d_tot := by sorry

theorem longer_distance_takes_longer (v0 : Float) (slope : Float)
  (h1 : 3.1 ≤ v0 ∧ v0 ≤ 100)
  (h2 : -30 ≤ slope ∧ slope ≤ 30)
  (h3 : temps v0 slope 10 ≠ -1)
  (h4 : temps v0 slope 20 ≠ -1) :
  temps v0 slope 20 > temps v0 slope 10 := by sorry

theorem faster_initial_speed_faster (d_tot slope : Float)
  (h1 : -30 ≤ slope ∧ slope ≤ 30) 
  (h2 : 0.1 ≤ d_tot ∧ d_tot ≤ 1000)
  (h3 : temps 20 slope d_tot ≠ -1)
  (h4 : temps 30 slope d_tot ≠ -1) :
  temps 30 slope d_tot ≤ temps 20 slope d_tot := by sorry
-- </vc-theorems>