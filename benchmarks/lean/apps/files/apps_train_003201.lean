-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def move (position : Int) (roll : Int) : Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem move_roll_proportional 
  (position roll : Int) 
  (h : 1 ≤ roll ∧ roll ≤ 6) : 
  move position roll = position + 2 * roll :=
  sorry

theorem move_relative_distance
  (position : Int) :
  move position 1 < move position 6 :=
  sorry

/-
info: 8
-/
-- #guard_msgs in
-- #eval move 0 4

/-
info: 15
-/
-- #guard_msgs in
-- #eval move 3 6

/-
info: 12
-/
-- #guard_msgs in
-- #eval move 2 5
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible