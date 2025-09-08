/-
=====Problem Statement=====
When users post an update on social media,such as a URL, image, status update etc., other users in their network are able to view this new post on their news feed. Users can also see exactly when the post was published, i.e, how many hours, minutes or seconds ago.
Since sometimes posts are published and viewed in different time zones, this can be confusing. You are given two timestamps of one such post that a user can see on his newsfeed in the following format:
Day dd Mon yyyy hh:mm:ss +xxxx
Here +xxxx represents the time zone. Your task is to print the absolute difference (in seconds) between them.

=====Input Format=====
The first line contains T, the number of tescases.
Each testcase contains 2 lines, representing time t_1 and time t_2.
-/

def parseDateTime (s : String) : DateTime := sorry

def absTimeDiffInSeconds (t1 t2 : DateTime) : Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

def timeDifference (ts1 ts2 : String) : Nat := sorry

theorem timeDiff_nonneg (ts1 ts2 : String) :
  timeDifference ts1 ts2 ≥ 0 := sorry

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

-- Apps difficulty: introductory
-- Assurance level: guarded