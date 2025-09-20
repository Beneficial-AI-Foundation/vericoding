-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def day_and_time (mins : Int) : String :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem day_and_time_valid_format (mins : Int) :
  let result := day_and_time mins
  let parts := result.splitOn " "
  let day := parts[0]!
  let time := parts[1]!
  let hours_mins := time.splitOn ":"
  let hours := hours_mins[0]!.toInt!
  let minutes := hours_mins[1]!.toInt!
  parts.length = 2 ∧
  (day = "Monday" ∨ day = "Tuesday" ∨ day = "Wednesday" ∨
   day = "Thursday" ∨ day = "Friday" ∨ day = "Saturday" ∨ day = "Sunday") ∧
  0 ≤ hours ∧ hours ≤ 23 ∧
  0 ≤ minutes ∧ minutes ≤ 59 :=
sorry

theorem day_and_time_weekly_cycle (mins : Int) :
  day_and_time mins = day_and_time (mins + 7*24*60) :=
sorry
-- </vc-theorems>