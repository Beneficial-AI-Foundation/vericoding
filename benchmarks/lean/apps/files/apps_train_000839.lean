-- <vc-helpers>
-- </vc-helpers>

def count_fibonacci_in_range (a b : Int) : Nat :=
  sorry

theorem zero_range_is_zero :
  count_fibonacci_in_range 0 0 = 0 :=
  sorry

/-
info: 5
-/
-- #guard_msgs in
-- #eval count_fibonacci_in_range 10 100

/-
info: 4
-/
-- #guard_msgs in
-- #eval count_fibonacci_in_range 1234567890 9876543210

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_fibonacci_in_range 0 0

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible