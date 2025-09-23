-- <vc-preamble>
def List.sum (xs: List Int) : Int :=
  match xs with
  | [] => 0
  | x::rest => x + sum rest
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def jobScheduling (startTimes endTimes profits: List Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem job_scheduling_basic_properties 
  (startTimes endTimes profits: List Int)
  (h1: startTimes.length = endTimes.length)
  (h2: endTimes.length = profits.length)
  (h3: ∀ i, i < startTimes.length → startTimes[i]! > 0)
  (h4: ∀ i, i < endTimes.length → endTimes[i]! > startTimes[i]!)
  (h5: ∀ i, i < profits.length → profits[i]! > 0) :
  let result := jobScheduling startTimes endTimes profits
  -- Result is non-negative
  result ≥ 0 ∧
  -- Result doesn't exceed sum of profits  
  result ≤ List.sum profits :=
  sorry

theorem job_scheduling_single_job
  (startTime endTime profit: Int)
  (h1: startTime > 0)
  (h2: endTime > startTime)
  (h3: profit > 0) :
  jobScheduling [startTime] [endTime] [profit] = profit :=
  sorry

/-
info: 120
-/
-- #guard_msgs in
-- #eval jobScheduling [1, 2, 3, 3] [3, 4, 5, 6] [50, 10, 40, 70]

/-
info: 150
-/
-- #guard_msgs in
-- #eval jobScheduling [1, 2, 3, 4, 6] [3, 5, 10, 6, 9] [20, 20, 100, 70, 60]

/-
info: 6
-/
-- #guard_msgs in
-- #eval jobScheduling [1, 1, 1] [2, 3, 4] [5, 6, 4]
-- </vc-theorems>