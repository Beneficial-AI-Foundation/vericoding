-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_min_time_difference (times: List String) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem exceeding_size_gives_zero (times: List String)
  (h: times.length > 1440) :
  find_min_time_difference times = 0 :=
  sorry

theorem wrap_around_case :
  find_min_time_difference ["23:59", "00:00"] = 1 :=
  sorry
-- </vc-theorems>