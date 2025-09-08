/-
###Instructions

Write a function that takes a negative or positive integer, which represents the number of minutes before (-) or after (+) Sunday midnight, and returns the current day of the week and the current time in 24hr format ('hh:mm') as a string. 

```python
day_and_time(0)       should return 'Sunday 00:00'
day_and_time(-3)      should return 'Saturday 23:57'
day_and_time(45)      should return 'Sunday 00:45'
day_and_time(759)     should return 'Sunday 12:39'
day_and_time(1236)    should return 'Sunday 20:36'
day_and_time(1447)    should return 'Monday 00:07'
day_and_time(7832)    should return 'Friday 10:32'
day_and_time(18876)   should return 'Saturday 02:36'
day_and_time(259180)  should return 'Thursday 23:40' 
day_and_time(-349000) should return 'Tuesday 15:20'
```
-/

-- <vc-helpers>
-- </vc-helpers>

def day_and_time (mins : Int) : String := sorry

/- For any integer minutes, the output matches expected day/time format -/

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
  0 ≤ minutes ∧ minutes ≤ 59 := sorry

/- Output repeats on weekly cycle -/

theorem day_and_time_weekly_cycle (mins : Int) :
  day_and_time mins = day_and_time (mins + 7*24*60) := sorry

/-
info: 'Sunday 00:00'
-/
-- #guard_msgs in
-- #eval day_and_time 0

/-
info: 'Saturday 23:57'
-/
-- #guard_msgs in
-- #eval day_and_time -3

/-
info: 'Monday 00:07'
-/
-- #guard_msgs in
-- #eval day_and_time 1447

-- Apps difficulty: introductory
-- Assurance level: unguarded