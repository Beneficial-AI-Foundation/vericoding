-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def HasCommonElement (a b : Array Int) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem HasCommonElement_spec (a b : Array Int) :
(HasCommonElement a b = true →
∃ i j, 0 ≤ i ∧ i < a.size ∧ 0 ≤ j ∧ j < b.size ∧ a[i]! = b[j]!) ∧
(HasCommonElement a b = false →
∀ i j, 0 ≤ i ∧ i < a.size ∧ 0 ≤ j ∧ j < b.size → a[i]! ≠ b[j]!) :=
sorry
-- </vc-theorems>