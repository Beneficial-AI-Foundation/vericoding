-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def RemoveDuplicates (a : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem RemoveDuplicates_spec (a : Array Int) :
let result := RemoveDuplicates a
(∀ x, (result.contains x ↔ ∃ i, 0 ≤ i ∧ i < a.size ∧ a[i]! = x)) ∧
(∀ i j, 0 ≤ i ∧ i < j ∧ j < result.size → result[i]! ≠ result[j]!) :=
sorry
-- </vc-theorems>