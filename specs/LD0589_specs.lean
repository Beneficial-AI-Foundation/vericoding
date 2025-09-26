-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ZapNegatives (a : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ZapNegatives_spec (a : Array Int) :
let result := ZapNegatives a
(∀ i, 0 ≤ i ∧ i < a.size →
(if (a[i]! < 0) then result[i]! = 0
else result[i]! = a[i]!)) ∧
result.size = a.size :=
sorry
-- </vc-theorems>