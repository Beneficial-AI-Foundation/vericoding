-- <vc-helpers>
-- </vc-helpers>

def routes (n : Int) : Int := sorry

def factorial (n : Int) : Int := sorry

theorem routes_formula {n : Int} (h : n > 0) : 
  routes n = factorial (2*n) / (factorial n * factorial n) := sorry

theorem routes_non_positive {n : Int} (h : n ≤ 0) :
  routes n = 0 := sorry

theorem routes_monotonic {n : Int} (h1 : n > 1) :
  routes n > routes (n-1) := sorry 

theorem routes_initial_values :
  routes 1 = 2 ∧ routes 2 = 6 ∧ routes 3 = 20 := sorry

/-
info: 2
-/
-- #guard_msgs in
-- #eval routes 1

/-
info: 6
-/
-- #guard_msgs in
-- #eval routes 2

/-
info: 0
-/
-- #guard_msgs in
-- #eval routes -100

-- Apps difficulty: introductory
-- Assurance level: unguarded