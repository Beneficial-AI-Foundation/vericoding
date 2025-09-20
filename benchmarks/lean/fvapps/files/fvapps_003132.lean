-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def converter (mpg : Float) : Float := sorry 

namespace converter
-- </vc-definitions>

-- <vc-theorems>
theorem converter_positive {mpg : Float} (h : mpg ≥ 1) : converter mpg > 0 := sorry 

theorem converter_proportional {mpg : Float} (h1 : mpg ≥ 1) (h2 : mpg ≤ 500) : 
  0.30 * mpg ≤ converter mpg ∧ converter mpg ≤ 0.40 * mpg := sorry

end converter
-- </vc-theorems>