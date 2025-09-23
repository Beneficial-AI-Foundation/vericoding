-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def List.variance (l : List Int) : Float := sorry

def regressionLine (x : List Int) (y : List Int) : Float × Float := sorry
-- </vc-definitions>

-- <vc-theorems>
theorem regression_line_outputs_float_pair 
  (x y : List Int) 
  (h1 : x.length ≥ 3) 
  (h2 : y.length = x.length)
  (h3 : (List.variance x) > 0) :
  let (a, b) := regressionLine x y
  ∃ (a' b' : Float), a = a' ∧ b = b' := sorry

theorem regression_line_outputs_finite 
  (x y : List Int)
  (h1 : x.length ≥ 3)
  (h2 : y.length = x.length) 
  (h3 : (List.variance x) > 0) :
  let (a, b) := regressionLine x y
  ¬a.isNaN ∧ ¬b.isNaN := sorry
-- </vc-theorems>