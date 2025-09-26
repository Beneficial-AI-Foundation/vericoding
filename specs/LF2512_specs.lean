-- <vc-preamble>
def parseDateTime (s : String) : DateTime := sorry

def absTimeDiffInSeconds (t1 t2 : DateTime) : Nat := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def timeDifference (ts1 ts2 : String) : Nat := sorry

theorem timeDiff_nonneg (ts1 ts2 : String) :
  timeDifference ts1 ts2 ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem timeDiff_commutative (ts1 ts2 : String) :
  timeDifference ts1 ts2 = timeDifference ts2 ts1 := sorry

theorem timeDiff_matches_datetime (ts1 ts2 : String) :
  let dt1 := parseDateTime ts1
  let dt2 := parseDateTime ts2
  timeDifference ts1 ts2 = absTimeDiffInSeconds dt1 dt2 := sorry

theorem timeDiff_same_timestamp (ts : String) :
  timeDifference ts ts = 0 := sorry

/-
info: 25200
-/
-- #guard_msgs in
-- #eval time_difference "Sun 10 May 2015 13:54:36 -0700" "Sun 10 May 2015 13:54:36 -0000"

/-
info: 88200
-/
-- #guard_msgs in
-- #eval time_difference "Sat 02 May 2015 19:54:36 +0530" "Fri 01 May 2015 13:54:36 -0000"
-- </vc-theorems>