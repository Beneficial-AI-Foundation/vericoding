-- <vc-preamble>
def sorted (a : Array Int) : Prop :=
∀ i, 0 < i ∧ i < a.size → a[i-1]! ≤ a[i]!
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def FindMin (a : Array Int) (lo : Nat) : Nat :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem FindMin_spec (a : Array Int) (lo : Nat) :
a.size > 0 ∧ lo < a.size →
let minIdx := FindMin a lo
minIdx ≥ lo ∧ minIdx < a.size ∧
(∀ x, lo ≤ x ∧ x < a.size → a[minIdx]! ≤ a[x]!) :=
sorry
-- </vc-theorems>