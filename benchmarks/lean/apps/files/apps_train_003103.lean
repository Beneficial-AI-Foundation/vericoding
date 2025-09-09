-- <vc-helpers>
-- </vc-helpers>

def count (n : Int) : Int := sorry

theorem count_monotonic {n : Int} (h : n ≥ 5) : 
  count n ≥ count (n-1) := sorry

theorem count_negative_input {n : Int} (h : n < 0) : 
  count n = sorry := sorry

/-
info: 3
-/
-- #guard_msgs in
-- #eval count 5

/-
info: 65
-/
-- #guard_msgs in
-- #eval count 50

/-
info: 1135
-/
-- #guard_msgs in
-- #eval count 500

-- Apps difficulty: introductory
-- Assurance level: guarded