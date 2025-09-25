-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def numPoints (points : List Point) (r : Float) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem numPoints_bounds {points : List Point} {r : Float} 
  (h1 : r > 0)
  (h2 : points ≠ []) :
  1 ≤ numPoints points r ∧ numPoints points r ≤ points.length :=
sorry

theorem numPoints_tiny_radius {points : List Point} 
  (h1 : points ≠ [])
  (h2 : r = 0.1) :
  numPoints points r = 1 :=
sorry

theorem numPoints_huge_radius {points : List Point}
  (h1 : points ≠ [])
  (h2 : r = 1000) :
  numPoints points r = points.length :=
sorry

theorem numPoints_shuffle {points perm : List Point} {r : Float}
  (h1 : r > 0)
  (h2 : perm.length = points.length)
  (h3 : ∀ p, p ∈ points ↔ p ∈ perm) :
  numPoints points r = numPoints perm r :=
sorry

theorem numPoints_single_point {r : Float}
  (h : r > 0) :
  numPoints [Point.mk 0 0] r = 1 :=
sorry

theorem numPoints_exact_radius :
  numPoints [Point.mk 0 0, Point.mk 2 0] 1 = 2 :=
sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval numPoints [[-2, 0], [2, 0], [0, 2], [0, -2]] 2

/-
info: 5
-/
-- #guard_msgs in
-- #eval numPoints [[-3, 0], [3, 0], [2, 6], [5, 4], [0, 9], [7, 8]] 5

/-
info: 4
-/
-- #guard_msgs in
-- #eval numPoints [[1, 2], [3, 5], [1, -1], [2, 3], [4, 1], [1, 3]] 2
-- </vc-theorems>