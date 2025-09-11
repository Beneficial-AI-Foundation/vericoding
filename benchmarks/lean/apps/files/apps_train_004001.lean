-- <vc-preamble>
def isValidTriangle (a b c : Float) : Prop :=
  (a + b > c) ∧ (b + c > a) ∧ (a + c > b)

def calculateArea (a b c : Float) : Float :=
  let s := (a + b + c) / 2
  Float.sqrt (s * (s - a) * (s - b) * (s - c))

def equableTriangle (a b c : Float) : Bool :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isClose (x y : Float) (tol : Float) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem equable_triangle_isosceles {x : Float} (h : x > 0)
  (hvalid : isValidTriangle x x x) :
  equableTriangle x x x = isClose (calculateArea x x x) (3 * x) 0.0001 := by
  sorry

theorem equable_triangle_general {a b c : Float} (ha : a > 0) (hb : b > 0) (hc : c > 0)
  (hvalid : isValidTriangle a b c) :
  equableTriangle a b c = isClose (calculateArea a b c) (a + b + c) 0.0001 := by
  sorry

/-
info: True
-/
-- #guard_msgs in
-- #eval equable_triangle 5 12 13

/-
info: False
-/
-- #guard_msgs in
-- #eval equable_triangle 2 3 4

/-
info: True
-/
-- #guard_msgs in
-- #eval equable_triangle 6 25 29
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded