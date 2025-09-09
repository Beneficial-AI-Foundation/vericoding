-- <vc-helpers>
-- </vc-helpers>

def solve_vaccine_distribution (N D : Nat) (ages : List Nat) : Nat :=
  sorry

theorem vaccine_distribution_positive (N D : Nat) (ages : List Nat) 
    (h1 : N > 0) (h2 : D > 0) (h3 : ages.length > 0) :
  solve_vaccine_distribution N D ages > 0 := sorry

theorem vaccine_distribution_D_one (N D : Nat) (ages : List Nat)
    (h : D = 1) (h1 : N > 0) :
  solve_vaccine_distribution N D ages = N := sorry

theorem vaccine_distribution_min_days (N D : Nat) (ages : List Nat)
    (h1 : N > 0) (h2 : D > 0) :
  solve_vaccine_distribution N D ages ≥ (N + D - 1) / D := sorry

/-
info: 10
-/
-- #guard_msgs in
-- #eval solve_vaccine_distribution 10 1 [10, 20, 30, 40, 50, 60, 90, 80, 100, 1]

/-
info: 3
-/
-- #guard_msgs in
-- #eval solve_vaccine_distribution 5 2 [9, 80, 27, 72, 79]

/-
info: 2
-/
-- #guard_msgs in
-- #eval solve_vaccine_distribution 3 2 [80, 90, 100]

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible