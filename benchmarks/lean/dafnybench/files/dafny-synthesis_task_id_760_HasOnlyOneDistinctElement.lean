-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def HasOnlyOneDistinctElement (a : Array Int) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem HasOnlyOneDistinctElement_spec (a : Array Int) :
(HasOnlyOneDistinctElement a = true →
∀ i j, 0 ≤ i ∧ i < a.size ∧ 0 ≤ j ∧ j < a.size → a[i]! = a[j]!) ∧
(HasOnlyOneDistinctElement a = false →
∃ i j, 0 ≤ i ∧ i < a.size ∧ 0 ≤ j ∧ j < a.size ∧ a[i]! ≠ a[j]!) :=
sorry
-- </vc-theorems>