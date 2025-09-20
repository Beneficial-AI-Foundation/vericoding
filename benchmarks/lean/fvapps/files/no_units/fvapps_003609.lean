-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def hoop_count (n : Int) : String := sorry

theorem hoop_count_return_value (n : Int) :
  (hoop_count n = "Keep at it until you get it") ∨
  (hoop_count n = "Great, now move on to tricks") := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem hoop_count_less_than_ten (n : Int) :
  n < 10 → hoop_count n = "Keep at it until you get it" := sorry

theorem hoop_count_ten_or_more (n : Int) :
  n ≥ 10 → hoop_count n = "Great, now move on to tricks" := sorry
-- </vc-theorems>