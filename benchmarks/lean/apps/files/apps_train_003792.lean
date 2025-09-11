-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def area_of_polygon_inside_circle (r : Float) (n : Nat) : Float := sorry 

theorem area_always_positive {r : Float} {n : Nat} 
  (h1 : r > 0)
  (h2 : n ≥ 3) :
  area_of_polygon_inside_circle r n > 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem area_increases_with_radius {r : Float} {n : Nat}
  (h1 : r > 0) 
  (h2 : n ≥ 3) :
  area_of_polygon_inside_circle (2*r) n > area_of_polygon_inside_circle r n := sorry

theorem area_maximal_for_larger_n {r : Float} {n : Nat}
  (h1 : r > 0)
  (h2 : n ≥ 3) :
  area_of_polygon_inside_circle r n ≥ area_of_polygon_inside_circle r 3 := sorry

/-
info: 11.691
-/
-- #guard_msgs in
-- #eval area_of_polygon_inside_circle 3 3

/-
info: 8.0
-/
-- #guard_msgs in
-- #eval area_of_polygon_inside_circle 2 4

/-
info: 14.86
-/
-- #guard_msgs in
-- #eval area_of_polygon_inside_circle 2.5 5
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: unguarded