-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def calculate_years (principal interest tax desired : Float) : Nat :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem calculate_years_non_negative (principal interest tax desired : Float)
  (h1 : principal - desired > 1 ∨ desired - principal > 1)
  (h2 : interest ≥ 0.01) (h3 : interest ≤ 0.2) 
  (h4 : tax ≥ 0) (h5 : tax ≤ 0.5)
  (h6 : principal ≥ 100) (h7 : principal ≤ 10000)
  (h8 : desired ≥ 100) (h9 : desired ≤ 10000) :
  calculate_years principal interest tax desired ≥ 0 := 
  sorry

theorem years_zero_if_principal_geq_desired (principal interest tax desired : Float)
  (h1 : principal - desired > 1 ∨ desired - principal > 1)
  (h2 : interest ≥ 0.01) (h3 : interest ≤ 0.2)
  (h4 : tax ≥ 0) (h5 : tax ≤ 0.5)
  (h6 : principal ≥ 100) (h7 : principal ≤ 10000)
  (h8 : desired ≥ 100) (h9 : desired ≤ 10000)
  (h10 : principal ≥ desired) :
  calculate_years principal interest tax desired = 0 :=
  sorry

theorem years_positive_if_desired_gt_principal (principal interest tax desired : Float)
  (h1 : principal - desired > 1 ∨ desired - principal > 1)
  (h2 : interest ≥ 0.01) (h3 : interest ≤ 0.2)
  (h4 : tax ≥ 0) (h5 : tax ≤ 0.5) 
  (h6 : principal ≥ 100) (h7 : principal ≤ 10000)
  (h8 : desired ≥ 100) (h9 : desired ≤ 10000)
  (h10 : desired > principal) :
  calculate_years principal interest tax desired ≥ 1 :=
  sorry

theorem same_amount_returns_zero (principal interest tax : Float)
  (h1 : interest ≥ 0.01) (h2 : interest ≤ 0.2)
  (h3 : tax ≥ 0) (h4 : tax ≤ 0.5)
  (h5 : principal ≥ 100) (h6 : principal ≤ 10000) :
  calculate_years principal interest tax principal = 0 :=
  sorry
-- </vc-theorems>