-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def can_meet (pos1 pos2 speed1 speed2 : Int) : String :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem same_positions_always_meets (pos : Int) :
  can_meet pos pos speed1 speed2 = "YES" := by sorry

theorem same_speeds_never_meets (pos1 pos2 speed : Int) :
  pos1 ≠ pos2 → can_meet pos1 pos2 speed speed = "NO" := by sorry

theorem meeting_requires_divisible_difference 
  (pos1 pos2 speed1 speed2 : Int)
  (h1 : speed1 ≠ speed2)
  (h2 : (pos1 - pos2).natAbs % (speed1 - speed2).natAbs = 0) :
  can_meet pos1 pos2 speed1 speed2 = "YES" := by sorry

theorem meeting_impossible_if_not_divisible
  (pos1 pos2 speed1 speed2 : Int)
  (h1 : speed1 ≠ speed2) 
  (h2 : (pos1 - pos2).natAbs % (speed1 - speed2).natAbs ≠ 0) :
  can_meet pos1 pos2 speed1 speed2 = "NO" := by sorry

/-
info: 'YES'
-/
-- #guard_msgs in
-- #eval can_meet 3 4 1 2

/-
info: 'NO'
-/
-- #guard_msgs in
-- #eval can_meet 10 20 3 7

/-
info: 'YES'
-/
-- #guard_msgs in
-- #eval can_meet 5 5 2 3
-- </vc-theorems>