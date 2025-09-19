-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def solve_vaccine_distribution (N D : Nat) (ages : List Nat) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem vaccine_distribution_positive (N D : Nat) (ages : List Nat) 
    (h1 : N > 0) (h2 : D > 0) (h3 : ages.length > 0) :
  solve_vaccine_distribution N D ages > 0 := sorry

theorem vaccine_distribution_D_one (N D : Nat) (ages : List Nat)
    (h : D = 1) (h1 : N > 0) :
  solve_vaccine_distribution N D ages = N := sorry

theorem vaccine_distribution_min_days (N D : Nat) (ages : List Nat)
    (h1 : N > 0) (h2 : D > 0) :
  solve_vaccine_distribution N D ages ≥ (N + D - 1) / D := sorry
-- </vc-theorems>