-- <vc-preamble>
def predict (model : Datamining) (x : Float) : Float :=
  sorry
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def abs (x : Float) : Float :=
  if x < 0 then -x else x
-- </vc-definitions>

-- <vc-theorems>
theorem fit_predict_linear_midpoint
  (train_set : List (Int × Int))
  (distinct_xs : ∀ (p1 p2 : Int × Int), p1 ∈ train_set → p2 ∈ train_set → p1.1 = p2.1 → p1 = p2)
  (size_geq_2 : train_set.length ≥ 2)
  (model : Datamining) : let y1 := predict model 0; let y2 := predict model 1; let y3 := predict model 0.5; let expected_y3 := y1 + (y2 - y1) * 0.5; abs (y3 - expected_y3) < 1e-10 :=
  sorry
-- </vc-theorems>