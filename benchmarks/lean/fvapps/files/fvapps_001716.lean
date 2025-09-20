-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Point := Float × Float

def convex_hull_area (points : List Point) : Float :=
  sorry

def is_internal_point (p : Point) (points : List Point) : Prop :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
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
-- </vc-theorems>