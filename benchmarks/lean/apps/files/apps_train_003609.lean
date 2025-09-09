-- <vc-helpers>
-- </vc-helpers>

def hoop_count (n : Int) : String := sorry

theorem hoop_count_return_value (n : Int) :
  (hoop_count n = "Keep at it until you get it") ∨
  (hoop_count n = "Great, now move on to tricks") := sorry

theorem hoop_count_less_than_ten (n : Int) :
  n < 10 → hoop_count n = "Keep at it until you get it" := sorry

theorem hoop_count_ten_or_more (n : Int) :
  n ≥ 10 → hoop_count n = "Great, now move on to tricks" := sorry

/-
info: 'Keep at it until you get it'
-/
-- #guard_msgs in
-- #eval hoop_count 6

/-
info: 'Great, now move on to tricks'
-/
-- #guard_msgs in
-- #eval hoop_count 10

/-
info: 'Great, now move on to tricks'
-/
-- #guard_msgs in
-- #eval hoop_count 22

-- Apps difficulty: introductory
-- Assurance level: unguarded