-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def travel (totalTime: Int) (runTime: Int) (restTime: Int) (speed: Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem travel_distance_bounded
  (totalTime: Int) (runTime: Int) (restTime: Int) (speed: Int)
  (h1: totalTime > 0) (h2: runTime > 0) (h3: restTime ≥ 0) (h4: speed > 0) :
  let dist := travel totalTime runTime restTime speed
  dist ≤ totalTime * speed ∧ dist ≥ 0 ∧ dist % speed = 0 :=
sorry

theorem travel_no_rest
  (totalTime: Int) (runTime: Int) (speed: Int)
  (h1: totalTime > 0) (h2: runTime > 0) (h3: speed > 0) :
  travel totalTime runTime 0 speed = totalTime * speed :=
sorry

theorem travel_invalid_total_time
  (totalTime: Int) (runTime: Int) (restTime: Int) (speed: Int)
  (h1: totalTime ≤ 0) (h2: runTime > 0) (h3: restTime ≥ 0) (h4: speed > 0) :
  travel totalTime runTime restTime speed = 0 :=
sorry

theorem travel_invalid_run_time
  (totalTime: Int) (runTime: Int) (restTime: Int) (speed: Int)
  (h1: totalTime > 0) (h2: runTime ≤ 0) (h3: restTime ≥ 0) (h4: speed > 0) :
  travel totalTime runTime restTime speed = 0 :=
sorry

theorem travel_invalid_speed
  (totalTime: Int) (runTime: Int) (restTime: Int) (speed: Int)
  (h1: totalTime > 0) (h2: runTime > 0) (h3: restTime ≥ 0) (h4: speed ≤ 0) :
  travel totalTime runTime restTime speed = 0 :=
sorry
-- </vc-theorems>