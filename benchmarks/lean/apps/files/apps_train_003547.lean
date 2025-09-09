-- <vc-helpers>
-- </vc-helpers>

def minimum (l : List Int) : Int := sorry
def maximum (l : List Int) : Int := sorry

theorem min_leq_all_elements (l : List Int) (h : l ≠ []) :
  ∀ x ∈ l, minimum l ≤ x := sorry

theorem max_geq_all_elements (l : List Int) (h : l ≠ []) :
  ∀ x ∈ l, maximum l ≥ x := sorry

theorem min_in_list (l : List Int) (h : l ≠ []) :
  minimum l ∈ l := sorry

theorem max_in_list (l : List Int) (h : l ≠ []) :
  maximum l ∈ l := sorry

theorem min_leq_max (l : List Int) (h : l ≠ []) :
  minimum l ≤ maximum l := sorry

theorem min_eq_max_singleton (l : List Int) (h : ∃ x, l = [x]) :
  minimum l = maximum l := sorry

/-
info: -110
-/
-- #guard_msgs in
-- #eval minimum [-52, 56, 30, 29, -54, 0, -110]

/-
info: 56
-/
-- #guard_msgs in
-- #eval maximum arr1

/-
info: 0
-/
-- #guard_msgs in
-- #eval minimum [42, 54, 65, 87, 0]

/-
info: 87
-/
-- #guard_msgs in
-- #eval maximum arr2

/-
info: 9
-/
-- #guard_msgs in
-- #eval minimum [9]

/-
info: 9
-/
-- #guard_msgs in
-- #eval maximum arr3

-- Apps difficulty: introductory
-- Assurance level: unguarded