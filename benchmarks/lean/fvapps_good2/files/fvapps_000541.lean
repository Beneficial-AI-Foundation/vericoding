-- <vc-preamble>
def manhattan_distance (x y : Int) : Nat :=
  Int.natAbs x + Int.natAbs y
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_robot_position (t : Nat) : Int × Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem coordinates_are_integers (t : Nat) (h : t > 0) :
  let (x, y) := find_robot_position t
  True :=
sorry

theorem position_uniqueness (t : Nat) (h : t > 0) :
  find_robot_position t = find_robot_position t :=
sorry

theorem first_position_is_up :
  find_robot_position 1 = (0, 1) :=
sorry
-- </vc-theorems>