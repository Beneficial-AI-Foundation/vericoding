-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def crusoe (n : Nat) (d ang dist_mult ang_mult : Float) : Float × Float :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem crusoe_results_finite (n : Nat) (d ang dist_mult ang_mult : Float)
  (h1 : 0 ≤ n ∧ n ≤ 100)
  (h2 : 0 ≤ d ∧ d ≤ 10) 
  (h3 : -360 ≤ ang ∧ ang ≤ 360)
  (h4 : 0.1 < dist_mult ∧ dist_mult ≤ 2.0)
  (h5 : 0.1 < ang_mult ∧ ang_mult ≤ 2.0) :
  let (x, y) := crusoe n d ang dist_mult ang_mult
  Float.isFinite x ∧ Float.isFinite y :=
sorry

theorem crusoe_zero_steps (d ang dist_mult ang_mult : Float) :
  crusoe 0 d ang dist_mult ang_mult = (0, 0) :=
sorry

theorem crusoe_zero_distance (ang dist_mult ang_mult : Float) :
  crusoe 1 0 ang dist_mult ang_mult = (0, 0) :=
sorry

theorem crusoe_symmetry (d ang : Float)
  (h1 : 0 ≤ d ∧ d ≤ 10)
  (h2 : -360 ≤ ang ∧ ang ≤ 360) :
  let (x1, y1) := crusoe 1 d ang 1.0 1.0
  let (x2, y2) := crusoe 1 d (ang + 180) 1.0 1.0
  x1 = -x2 ∧ y1 = -y2 := 
sorry
-- </vc-theorems>