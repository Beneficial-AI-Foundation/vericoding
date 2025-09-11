-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def nba_extrap (ppg mpg : Float) : Float := sorry

theorem nba_extrap_nonnegative 
  {ppg mpg : Float} (h1 : 0 ≤ ppg) (h2 : 0 < mpg) (h3 : mpg ≤ 48) :
  0 ≤ nba_extrap ppg mpg := 
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem nba_extrap_proportional
  {ppg mpg : Float} (h1 : 0 ≤ ppg) (h2 : 0 < mpg) (h3 : mpg ≤ 48) :
  nba_extrap ppg mpg = Float.round (48.0 * ppg / mpg) :=
sorry

theorem nba_extrap_zero :
  nba_extrap 0 0 = 0 :=
sorry

theorem nba_extrap_scaling_ratio
  {ppg mpg : Float} (h1 : 0 ≤ ppg) (h2 : 0 < mpg) (h3 : mpg ≤ 48) :
  nba_extrap ppg mpg = ppg * (48.0 / mpg) :=
sorry

/-
info: 28.8
-/
-- #guard_msgs in
-- #eval nba_extrap 12 20

/-
info: 48.0
-/
-- #guard_msgs in
-- #eval nba_extrap 10 10

/-
info: 14.1
-/
-- #guard_msgs in
-- #eval nba_extrap 5 17

/-
info: 0
-/
-- #guard_msgs in
-- #eval nba_extrap 0 0
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded