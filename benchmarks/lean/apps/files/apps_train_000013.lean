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

/-
info: 5
-/
-- #guard_msgs in
-- #eval calc_min_days 5 1 1

/-
info: 8
-/
-- #guard_msgs in
-- #eval calc_min_days 8 10 10

/-
info: 499999500000
-/
-- #guard_msgs in
-- #eval calc_min_days 1000000 1 1000000
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible