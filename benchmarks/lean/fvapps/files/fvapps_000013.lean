-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calc_min_days (n g b : Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem result_at_least_n {n g b : Nat} (hn : n > 0) (hg : g > 0) (hb : b > 0) :
  calc_min_days n g b ≥ n := 
  sorry

theorem result_at_least_high_quality {n g b : Nat} (hn : n > 0) (hg : g > 0) (hb : b > 0) :
  calc_min_days n g b ≥ (n + 1) / 2 :=
  sorry

theorem zero_bad_weather_equals_n {n g : Nat} (hn : n > 0) (hg : g > 0) :
  calc_min_days n g 0 = n :=
  sorry

theorem single_day_road {n : Nat} (hn : n > 0) :
  calc_min_days 1 n n = 1 :=
  sorry
-- </vc-theorems>