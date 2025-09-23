-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def IsSorted (a : Array Int) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem IsSorted_spec (a : Array Int) :
a.size > 0 →
(IsSorted a ↔ (∀ i j, 0 ≤ i ∧ i < j ∧ j < a.size → a[i]! ≤ a[j]!)) ∧
(¬IsSorted a → ∃ i j, 0 ≤ i ∧ i < j ∧ j < a.size ∧ a[i]! > a[j]!) :=
sorry
-- </vc-theorems>