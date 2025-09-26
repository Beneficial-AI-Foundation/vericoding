-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def CanyonSearch (a b : Array Int) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem CanyonSearch_spec (a b : Array Int) :
a.size ≠ 0 ∧ b.size ≠ 0 ∧
(∀ i j, 0 ≤ i → i < j → j < a.size → (a[i]!) ≤ (a[j]!)) ∧
(∀ i j, 0 ≤ i → i < j → j < b.size → (b[i]!) ≤ (b[j]!)) →
(∃ i j, 0 ≤ i ∧ i < a.size ∧ 0 ≤ j ∧ j < b.size ∧
CanyonSearch a b = if (a[i]!) < (b[j]!) then ((b[j]!) - (a[i]!)) else ((a[i]!) - (b[j]!))) ∧
(∀ i j, 0 ≤ i → i < a.size → 0 ≤ j → j < b.size →
CanyonSearch a b ≤ if (a[i]!) < (b[j]!) then ((b[j]!) - (a[i]!)) else ((a[i]!) - (b[j]!))) :=
sorry
-- </vc-theorems>