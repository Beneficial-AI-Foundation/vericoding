-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def symmetric_point (p q : List Int) : List Int := sorry

def distance (p q : List Int) : Float := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem symmetric_point_involution (p q : List Int) : 
  symmetric_point (symmetric_point p q) q = p := sorry

theorem symmetric_point_preserves_distance (p q : List Int) : 
  distance p q = distance q (symmetric_point p q) := sorry 

theorem symmetric_point_self_center (p : List Int) :
  symmetric_point p p = p := sorry

/-
info: [2, 2]
-/
-- #guard_msgs in
-- #eval symmetric_point [0, 0] [1, 1]

/-
info: [-6, -18]
-/
-- #guard_msgs in
-- #eval symmetric_point [2, 6] [-2, -6]

/-
info: [0, 0]
-/
-- #guard_msgs in
-- #eval symmetric_point [0, 0] [0, 0]
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded