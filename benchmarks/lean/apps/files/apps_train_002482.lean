def evaluatePolynomial (coeffs : List Float) (x : Float) : Float :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

def directPolynomial (coeffs : List Float) (x : Float) : Float :=
  sorry

theorem polynomial_evaluation_matches_direct 
  (coeffs : List Float) (x : Float)
  (h1 : coeffs.length ≥ 1)
  (h2 : coeffs.length ≤ 10)
  (h3 : ∀ c ∈ coeffs, -1000000 ≤ c ∧ c ≤ 1000000)
  (h4 : -100 ≤ x ∧ x ≤ 100) :
  evaluatePolynomial coeffs x - directPolynomial coeffs x ≤ 1e-10 * directPolynomial coeffs x :=
sorry 

theorem polynomial_at_zero
  (coeffs : List Float)
  (h1 : coeffs ≠ [])
  (h2 : coeffs.length ≤ 10)
  (h3 : ∀ c ∈ coeffs, -1000000 ≤ c ∧ c ≤ 1000000) :
  evaluatePolynomial coeffs 0 = coeffs.getLast h1 :=
sorry

-- Apps difficulty: introductory
-- Assurance level: guarded