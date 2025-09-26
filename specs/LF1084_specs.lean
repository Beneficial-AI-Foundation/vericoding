-- <vc-preamble>
def find_min_angle (t : Time) : String := sorry

def string_to_float (s : String) : Float := sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def round_float (f : Float) : Float := sorry

theorem find_min_angle_format (t : Time) : 
  ∃ n : Float, find_min_angle t = toString n ++ " degree" := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem find_min_angle_range (t : Time) :
  let angle := string_to_float (find_min_angle t)
  0 ≤ angle ∧ angle ≤ 180 := sorry 

theorem find_min_angle_precision (t : Time) :
  let angle := string_to_float (find_min_angle t)
  ∃ n : Float, angle = n ∧ n * 2 = round_float (n * 2) := sorry

theorem find_min_angle_12hr_symmetry (t : Time) :
  find_min_angle t = find_min_angle ⟨t.hours % 12, t.mins, sorry, t.m_valid⟩ := sorry

/-
info: '50 degree'
-/
-- #guard_msgs in
-- #eval find_min_angle "14:20"

/-
info: '5 degree'
-/
-- #guard_msgs in
-- #eval find_min_angle "02:10"

/-
info: '105 degree'
-/
-- #guard_msgs in
-- #eval find_min_angle "09:30"
-- </vc-theorems>