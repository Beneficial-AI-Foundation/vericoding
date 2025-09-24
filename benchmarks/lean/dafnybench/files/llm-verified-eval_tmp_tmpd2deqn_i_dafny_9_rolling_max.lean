-- <vc-preamble>
def isMax (m : Int) (numbers : Array Int) : Prop :=
numbers.contains m ∧
∀ i, 0 ≤ i ∧ i < numbers.size → numbers[i]! ≤ m
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def rolling_max (numbers : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem rolling_max_spec (numbers : Array Int) :
numbers.size > 0 →
let result := rolling_max numbers
result.size = numbers.size ∧
∀ i, 0 < i ∧ i < result.size →
isMax (result[i]!) (numbers.extract 0 (i + 1)) :=
sorry
-- </vc-theorems>