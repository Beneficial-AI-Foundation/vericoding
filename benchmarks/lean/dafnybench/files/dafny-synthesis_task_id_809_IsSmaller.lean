-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def IsSmaller (a b : Array Int) : Bool :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem IsSmaller_spec (a b : Array Int) :
a.size = b.size →
(IsSmaller a b ↔ (∀ i, 0 ≤ i ∧ i < a.size → a[i]! > b[i]!)) ∧
(!IsSmaller a b ↔ (∃ i, 0 ≤ i ∧ i < a.size ∧ a[i]! ≤ b[i]!)) :=
sorry
-- </vc-theorems>