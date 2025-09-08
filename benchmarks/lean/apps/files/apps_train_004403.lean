/-
You have recently discovered that horses travel in a unique pattern - they're either running (at top speed) or resting (standing still).

Here's an example of how one particular horse might travel:

```
The horse Blaze can run at 14 metres/second for 60 seconds, but must then rest for 45 seconds.

After 500 seconds Blaze will have traveled 4200 metres.
```

Your job is to write a function that returns how long a horse will have traveled after a given time.

####Input: 

* totalTime - How long the horse will be traveling (in seconds)

* runTime - How long the horse can run for before having to rest (in seconds)

* restTime - How long the horse have to rest for after running (in seconds)

* speed - The max speed of the horse (in metres/second)
-/

-- <vc-helpers>
-- </vc-helpers>

def travel (totalTime: Int) (runTime: Int) (restTime: Int) (speed: Int) : Int :=
  sorry

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

/-
info: 1120
-/
-- #guard_msgs in
-- #eval travel 1000 10 127 14

/-
info: 10000
-/
-- #guard_msgs in
-- #eval travel 1000 10 0 10

/-
info: 450
-/
-- #guard_msgs in
-- #eval travel 25 50 120 18

-- Apps difficulty: introductory
-- Assurance level: guarded