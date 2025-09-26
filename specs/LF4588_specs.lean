-- <vc-preamble>
def dist (p1 p2 : Point) : Float :=
  Float.sqrt ((p1.x - p2.x)^2 + (p1.y - p2.y)^2)

/- Given three points, returns the center and radius of their circumscribed circle -/

def circum_curvat (p₁ p₂ p₃ : Point) : Point × Float := sorry

/- Counts how many circles contain a given point -/
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def count_circles (circles : List (List Point)) (p : Point) : Nat := sorry

theorem count_circles_bounds {circles : List (List Point)} {p : Point} :
  0 ≤ count_circles circles p ∧ count_circles circles p ≤ circles.length := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem circle_contains_defining_points {p₁ p₂ p₃ : Point} :
  let (center, radius) := circum_curvat p₁ p₂ p₃
  dist p₁ center ≤ radius ∧ 
  dist p₂ center ≤ radius ∧
  dist p₃ center ≤ radius := sorry

/- Points used to define circle must not be collinear -/

theorem circle_points_not_collinear {p₁ p₂ p₃ : Point} 
  (h : circum_curvat p₁ p₂ p₃ = (center, radius)) :
  let area := Float.abs ((p₁.x * (p₂.y - p₃.y) + 
                         p₂.x * (p₃.y - p₁.y) + 
                         p₃.x * (p₁.y - p₂.y)) / 2)
  area > 0 := sorry

/-
info: 4
-/
-- #guard_msgs in
-- #eval count_circles [[[-3, 2], [1, 1], [6, 4]], [[-3, 2], [1, 1], [2, 6]], [[1, 1], [2, 6], [6, 4]], [[-3, 2], [2, 6], [6, 4]]] [1, 4]

/-
info: 0
-/
-- #guard_msgs in
-- #eval count_circles circles1 [10, 6]

/-
info: 4
-/
-- #guard_msgs in
-- #eval count_circles circles1 [2, 6]
-- </vc-theorems>