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
-- </vc-theorems>