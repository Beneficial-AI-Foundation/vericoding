-- <vc-helpers>
-- </vc-helpers>

def find_min_time_difference (times: List String) : Nat :=
  sorry

theorem exceeding_size_gives_zero (times: List String)
  (h: times.length > 1440) :
  find_min_time_difference times = 0 :=
  sorry

theorem wrap_around_case :
  find_min_time_difference ["23:59", "00:00"] = 1 :=
  sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval find_min_time_difference ["23:59", "00:00"]

/-
info: 0
-/
-- #guard_msgs in
-- #eval find_min_time_difference ["00:00", "23:59", "00:00"]

/-
info: 61
-/
-- #guard_msgs in
-- #eval find_min_time_difference ["01:01", "02:02", "03:03"]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible