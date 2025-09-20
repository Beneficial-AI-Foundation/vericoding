-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_race_encounters (x : Int) (r speed1 speed2 : Float) : Int :=
  sorry

def abs (x : Float) : Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem race_encounters_non_negative
  (x : Int) (r speed1 speed2 : Float)
  (h1 : x > 0)
  (h2 : r > 0)
  (h3 : speed1 > 0)
  (h4 : speed2 > 0)
  (h5 : Float.abs (speed1 - speed2) > 0.0001) :
  solve_race_encounters x r speed1 speed2 ≥ -1 :=
sorry

theorem race_encounters_less_than_laps
  (x : Int) (r speed1 speed2 : Float)
  (h1 : x > 0)
  (h2 : r > 0)
  (h3 : speed1 > 0)
  (h4 : speed2 > 0)
  (h5 : Float.abs (speed1 - speed2) > 0.0001) :
  solve_race_encounters x r speed1 speed2 < x :=
sorry

theorem race_encounters_speed_symmetry
  (x : Int) (r speed1 speed2 : Float)
  (h1 : x > 0)
  (h2 : r > 0)
  (h3 : speed1 > 0)
  (h4 : speed2 > 0)
  (h5 : Float.abs (speed1 - speed2) > 0.0001) :
  solve_race_encounters x r speed1 speed2 = solve_race_encounters x r speed2 speed1 :=
sorry

theorem race_encounters_speed_scaling
  (x : Int) (r speed1 speed2 : Float)
  (h1 : x > 0)
  (h2 : r > 0)
  (h3 : speed1 > 0)
  (h4 : speed2 > 0)
  (h5 : Float.abs (speed1 - speed2) > 0.0001) :
  solve_race_encounters x r speed1 speed2 = solve_race_encounters x r (2 * speed1) (2 * speed2) :=
sorry
-- </vc-theorems>