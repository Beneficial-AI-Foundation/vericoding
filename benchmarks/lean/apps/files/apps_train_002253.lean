-- <vc-preamble>
def Position := Int × Int × Bool × Bool × Bool × Bool

def find_robot_gather_point (robots : List Position) : List Int :=
sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def in_bounds (x y : Int) : Bool :=
-100000 ≤ x ∧ x ≤ 100000 ∧ -100000 ≤ y ∧ y ≤ 100000
-- </vc-definitions>

-- <vc-theorems>
theorem gather_point_valid (robots : List Position) :
  let result := find_robot_gather_point robots
  (result.length = 1 ∧ result = [0]) ∨ 
  (result.length = 3 ∧ 
   result.get! 0 = 1 ∧
   let x := result.get! 1
   let y := result.get! 2
   in_bounds x y ∧
   ∀ (robot : Position),
   robot ∈ robots →
   let (rx, ry, can_left, can_up, can_right, can_down) := robot
   (¬can_left → x ≥ rx) ∧
   (¬can_right → x ≤ rx) ∧
   (¬can_up → y ≤ ry) ∧
   (¬can_down → y ≥ ry)) :=
sorry

/-
info: [1, -1, -2]
-/
-- #guard_msgs in
-- #eval find_robot_gather_point [[-1, -2, 0, 0, 0, 0], [-1, -2, 0, 0, 0, 0]]

/-
info: [1, 2, 5]
-/
-- #guard_msgs in
-- #eval find_robot_gather_point [[1, 5, 1, 1, 1, 1], [2, 5, 0, 1, 0, 1], [3, 5, 1, 0, 0, 0]]

/-
info: [0]
-/
-- #guard_msgs in
-- #eval find_robot_gather_point [[1337, 1337, 0, 1, 1, 1], [1336, 1337, 1, 1, 0, 1]]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded