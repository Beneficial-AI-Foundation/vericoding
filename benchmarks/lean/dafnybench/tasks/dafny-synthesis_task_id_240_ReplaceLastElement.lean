-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ReplaceLastElement (first : Array Int) (second : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ReplaceLastElement_spec (first second : Array Int) :
first.size > 0 →
let result := ReplaceLastElement first second
result.size = first.size - 1 + second.size ∧
(∀ i, 0 ≤ i ∧ i < first.size - 1 → result[i]! = first[i]!) ∧
(∀ i, first.size - 1 ≤ i ∧ i < result.size → result[i]! = second[i - first.size + 1]!) :=
sorry
-- </vc-theorems>