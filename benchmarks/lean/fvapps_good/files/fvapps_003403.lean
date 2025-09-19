-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def quadratic (x1 x2 : Int) : Int × Int × Int :=
  sorry
-- </vc-definitions>

-- <vc-theorems>
theorem first_coeff_one (x1 x2 : Int) :
  let (a, b, c) := quadratic x1 x2
  a = 1 := sorry

theorem vieta_formulas (x1 x2 : Int) :
  let (a, b, c) := quadratic x1 x2
  (-b = x1 + x2) ∧ (c = x1 * x2) := sorry
-- </vc-theorems>