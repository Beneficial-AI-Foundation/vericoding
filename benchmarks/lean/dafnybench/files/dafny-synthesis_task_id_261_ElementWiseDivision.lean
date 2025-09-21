-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ElementWiseDivision (a b : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ElementWiseDivision_spec (a b : Array Int) :
(a.size = b.size) →
(∀ i, 0 ≤ i ∧ i < b.size → b[i]! ≠ 0) →
let result := ElementWiseDivision a b
(result.size = a.size) ∧
(∀ i, 0 ≤ i ∧ i < result.size → result[i]! = a[i]! / b[i]!) :=
sorry
-- </vc-theorems>