-- <vc-helpers>
-- </vc-helpers>

def find_angle_mbc (ab : Float) (bc : Float) : Float := sorry

theorem angle_properties (ab bc : Float)
  (h1 : ab > 0) (h2 : bc > 0)
  (h3 : ab < bc + bc) (h4 : bc < ab + ab) :
  let angle := find_angle_mbc ab bc
  0 < angle ∧ angle ≤ 90 := sorry

theorem equal_sides_angle (x : Float)
  (h1 : x > 0) :
  let angle := find_angle_mbc x x
  angle = 45 := sorry

theorem symmetric_inputs (x : Float)
  (h1 : x > 0) :
  find_angle_mbc x x = 45 := sorry

/-
info: '45°'
-/
-- #guard_msgs in
-- #eval find_angle_mbc 10 10

/-
info: '63°'
-/
-- #guard_msgs in
-- #eval find_angle_mbc 20 10

/-
info: '27°'
-/
-- #guard_msgs in
-- #eval find_angle_mbc 10 20

-- Apps difficulty: introductory
-- Assurance level: unguarded