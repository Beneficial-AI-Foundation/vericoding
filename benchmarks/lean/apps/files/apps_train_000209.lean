-- <vc-preamble>
def myPow (x : Float) (n : Int) : Float :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- <vc-helpers>
-- </vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def isClose (a b : Float) (relTol absTol : Float := 0.0) : Bool :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem myPow_matches_mathPow {x : Float} {n : Int} 
  (x_range : 0.1 ≤ x ∧ x ≤ 10)
  (n_range : -5 ≤ n ∧ n ≤ 5) :
  isClose (myPow x n) (Float.pow x (Float.ofInt n)) (relTol := 1e-5) (absTol := 1e-5) := 
  sorry

theorem myPow_zero_exponent {x : Float}  
  (x_range : 0.1 ≤ x ∧ x ≤ 10) :
  myPow x 0 = 1.0 :=
  sorry

theorem myPow_inverse_property {x : Float} {n : Int}
  (x_range : 0.1 ≤ x ∧ x ≤ 10)
  (n_range : 1 ≤ n ∧ n ≤ 2) :
  isClose ((myPow x n) * (myPow x (-n))) 1.0 (relTol := 1e-5) (absTol := 1e-5) :=
  sorry
-- </vc-theorems>

-- Apps difficulty: interview
-- Assurance level: guarded