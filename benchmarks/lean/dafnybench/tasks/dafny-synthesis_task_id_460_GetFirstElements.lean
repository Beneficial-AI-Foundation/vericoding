-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def GetFirstElements (lst : Array (Array Int)) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem GetFirstElements_spec (lst : Array (Array Int)) :
(∀ i, 0 ≤ i ∧ i < lst.size → (lst[i]!).size > 0) →
let result := GetFirstElements lst
result.size = lst.size ∧
(∀ i, 0 ≤ i ∧ i < result.size → result[i]! = (lst[i]!)[0]!) :=
sorry
-- </vc-theorems>