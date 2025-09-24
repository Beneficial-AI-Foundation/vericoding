-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def LucidNumbers (n : Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem LucidNumbers_spec (n : Int) :
n ≥ 0 →
let result := LucidNumbers n
(∀ i, 0 ≤ i ∧ i < result.size → (result[i]!) % 3 = 0) ∧
(∀ i, 0 ≤ i ∧ i < result.size → result[i]! ≤ n) ∧
(∀ i j, 0 ≤ i ∧ i < j ∧ j < result.size → result[i]! < result[j]!) :=
sorry
-- </vc-theorems>