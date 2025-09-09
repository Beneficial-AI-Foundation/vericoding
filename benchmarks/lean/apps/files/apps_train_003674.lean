-- <vc-helpers>
-- </vc-helpers>

def shape_area (n : Int) : Int := sorry

theorem shape_area_positive {n : Int} (h : n > 0) : shape_area n > 0 := sorry

theorem shape_area_formula {n : Int} : shape_area n = n^2 + (n-1)^2 := sorry

theorem shape_area_strictly_increasing {n : Int} (h : n > 1) : 
  shape_area n > shape_area (n-1) := sorry

theorem shape_area_diff_increasing {n : Int} (h : n > 2) :
  shape_area n - shape_area (n-1) > shape_area (n-1) - shape_area (n-2) := sorry

theorem shape_area_returns_int {n : Int} : ∃ (m : Int), shape_area n = m := sorry

/-
info: 1
-/
-- #guard_msgs in
-- #eval shape_area 1

/-
info: 5
-/
-- #guard_msgs in
-- #eval shape_area 2

/-
info: 13
-/
-- #guard_msgs in
-- #eval shape_area 3

-- Apps difficulty: introductory
-- Assurance level: guarded