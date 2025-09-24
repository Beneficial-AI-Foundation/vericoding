-- <vc-preamble>
def Time.toString (t : Time) : String := sorry

def parseTime (s : String) : Option Time := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve (times : List String) : String := sorry

def toMinutes (t : Time) : Nat :=
  t.hour * 60 + t.minute
-- </vc-definitions>

-- <vc-theorems>
theorem solve_valid_format (times : List String) :
  let result := solve times
  let hrs := result.take 2
  let mins := result.drop 3
  result.length = 5 ∧ 
  result.data.get? 2 = some ':' ∧
  (parseTime result).isSome := sorry

theorem solve_under_24h (times : List String) :
  let result := solve times
  let t := Option.get! (parseTime result)
  toMinutes t < 24 * 60 := sorry

theorem solve_single_time (t : Time) :
  solve [t.toString] = "23:59" := sorry

theorem solve_unique_times (times : List String) :
  solve times = solve (times ++ times) := sorry

/-
info: '23:59'
-/
-- #guard_msgs in
-- #eval solve ["14:51"]

/-
info: '11:40'
-/
-- #guard_msgs in
-- #eval solve ["23:00", "04:22", "18:05", "06:24"]

/-
info: '09:10'
-/
-- #guard_msgs in
-- #eval solve ["21:14", "15:34", "14:51", "06:25", "15:30"]
-- </vc-theorems>