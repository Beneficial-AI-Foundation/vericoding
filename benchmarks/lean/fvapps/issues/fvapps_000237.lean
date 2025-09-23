-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def is_robot_bounded (instructions : String) : Bool := sorry

theorem robot_boolean_output (instructions : String) :
  is_robot_bounded instructions = true ∨ is_robot_bounded instructions = false := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem empty_string_bounded :
  is_robot_bounded "" = true := sorry

theorem left_rotation_four_times (instructions : String) :
  is_robot_bounded ("LLLL" ++ instructions) = is_robot_bounded instructions := sorry

theorem right_rotation_four_times (instructions : String) :
  is_robot_bounded ("RRRR" ++ instructions) = is_robot_bounded instructions := sorry

theorem left_right_cancel (instructions : String) :
  is_robot_bounded ("LR" ++ instructions) = is_robot_bounded instructions := sorry

theorem north_unbounded :
  ∀ n : Nat, n > 0 → is_robot_bounded (String.mk (List.replicate n 'G')) = false := sorry

theorem turns_only_bounded (n : Nat) :
  is_robot_bounded (String.mk (List.join (List.replicate n ['L', 'R']))) = true := sorry

theorem full_rotation_bounded :
  is_robot_bounded "LLLL" = true ∧ is_robot_bounded "RRRR" = true := sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval is_robot_bounded "GGLLGG"

/-
info: False
-/
-- #guard_msgs in
-- #eval is_robot_bounded "GG"

/-
info: True
-/
-- #guard_msgs in
-- #eval is_robot_bounded "GL"
-- </vc-theorems>