-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def intersperse (numbers : Array Int) (delimiter : Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem intersperse_spec (numbers : Array Int) (delimiter : Int) :
let result := intersperse numbers delimiter
(result.size = if numbers.size > 0 then 2 * numbers.size - 1 else 0) ∧
(∀ i, 0 ≤ i ∧ i < result.size → i % 2 = 0 → result[i]! = numbers[i / 2]!) ∧
(∀ i, 0 ≤ i ∧ i < result.size → i % 2 = 1 → result[i]! = delimiter) :=
sorry
-- </vc-theorems>