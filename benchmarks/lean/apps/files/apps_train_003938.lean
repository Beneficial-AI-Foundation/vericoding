-- <vc-helpers>
-- </vc-helpers>

def rec (n : Int) : Int := sorry

theorem rec_non_negative (n : Int) : n ≥ 0 → rec n ≥ 0 := sorry

theorem rec_zero_or_negative (n : Int) : n ≤ 0 → rec n = 0 := sorry

theorem rec_strictly_increasing (n : Int) : n > 1 → rec n > rec (n-1) := sorry

theorem rec_grows_linearly (n : Int) : n > 1 → rec n ≥ n-1 := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval rec 0

/-
info: 12
-/
-- #guard_msgs in
-- #eval rec 5

/-
info: 837722
-/
-- #guard_msgs in
-- #eval rec 1000

-- Apps difficulty: introductory
-- Assurance level: guarded