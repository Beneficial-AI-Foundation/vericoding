-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def not_visible_cubes (n : Int) : Int := sorry

theorem not_visible_cubes_nonnegative (n : Int) (h : n ≥ 0) :
  not_visible_cubes n ≥ 0 := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem not_visible_cubes_small_cases (n : Int) (h : n ≤ 2) :
  not_visible_cubes (max 0 n) = 0 := sorry

theorem not_visible_cubes_large_cases (n : Int) (h : n ≥ 3) :
  not_visible_cubes n = (n - 2) ^ 3 := sorry

/-
info: 0
-/
-- #guard_msgs in
-- #eval not_visible_cubes 0

/-
info: 8
-/
-- #guard_msgs in
-- #eval not_visible_cubes 4

/-
info: 27
-/
-- #guard_msgs in
-- #eval not_visible_cubes 5
-- </vc-theorems>

-- Apps difficulty: introductory
-- Assurance level: guarded