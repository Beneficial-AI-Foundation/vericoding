def Point := Float × Float

def convex_hull_area (points : List Point) : Float :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def is_internal_point (p : Point) (points : List Point) : Prop :=
  sorry

theorem convex_hull_area_non_negative (points : List Point) :
  convex_hull_area points ≥ 0 :=
sorry

theorem convex_hull_area_less_than_three_points (points : List Point) :
  points.length < 3 → convex_hull_area points = 0 :=
sorry

theorem convex_hull_area_permutation_invariant {points perm : List Point} :
  points.length > 0 →
  points.Perm perm →
  convex_hull_area points = convex_hull_area perm :=
sorry

theorem convex_hull_area_internal_points {points : List Point} {p : Point} :
  points.length ≥ 3 →
  is_internal_point p points →
  convex_hull_area (p::points) = convex_hull_area points :=
sorry

/-
info: 6.0
-/
-- #guard_msgs in
-- #eval convex_hull_area [(0, 0), (0, 3), (4, 0)]

/-
info: 4.0
-/
-- #guard_msgs in
-- #eval convex_hull_area [(0, 0), (0, 2), (2, 2), (2, 0)]

/-
info: 6.0
-/
-- #guard_msgs in
-- #eval convex_hull_area [(0, 0), (0, 3), (4, 0), (1, 1), (2, 1)]

-- Apps difficulty: interview
-- Assurance level: unguarded