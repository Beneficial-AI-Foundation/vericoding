-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def distance_between_points (p1 p2 : Point) : Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem distance_symmetric (p1 p2 : Point) :
  distance_between_points p1 p2 = distance_between_points p2 p1 :=
  sorry

theorem distance_to_self (p : Point) :
  distance_between_points p p = 0 :=
  sorry

theorem triangle_inequality (p1 p2 p3 : Point) :
  distance_between_points p1 p3 ≤ 
  distance_between_points p1 p2 + distance_between_points p2 p3 :=
  sorry

theorem distance_matches_formula (p1 p2 : Point) :
  distance_between_points p1 p2 = 
  Float.sqrt ((p2.x - p1.x)^2 + (p2.y - p1.y)^2 + (p2.z - p1.z)^2) :=
  sorry

/-
info: 5.196152
-/
-- #guard_msgs in
-- #eval distance_between_points Point(1, 2, 3) Point(4, 5, 6)

/-
info: 1.732051
-/
-- #guard_msgs in
-- #eval distance_between_points Point(0, 0, 0) Point(1, 1, 1)

/-
info: 3.464102
-/
-- #guard_msgs in
-- #eval distance_between_points Point(-1, -1, -1) Point(1, 1, 1)
-- </vc-theorems>