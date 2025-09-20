-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def find_angle_mbc (ab : Float) (bc : Float) : Float := sorry

theorem angle_properties (ab bc : Float)
  (h1 : ab > 0) (h2 : bc > 0)
  (h3 : ab < bc + bc) (h4 : bc < ab + ab) :
  let angle := find_angle_mbc ab bc
  0 < angle ∧ angle ≤ 90 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem equal_sides_angle (x : Float)
  (h1 : x > 0) :
  let angle := find_angle_mbc x x
  angle = 45 := sorry

theorem symmetric_inputs (x : Float)
  (h1 : x > 0) :
  find_angle_mbc x x = 45 := sorry
-- </vc-theorems>