-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def QuicksortPartition (X : Array Int) (n : Int) (p : Int) : Int × Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem QuicksortPartition_spec
(X : Array Int) (n : Int) (p : Int) :
X.size ≥ 1 ∧ n = X.size →
let (a, b) := QuicksortPartition X n p
b ≥ n ∧
(∀ x, 0 ≤ x ∧ x < a ∧ a < n → X[x.toNat]! ≤ p) ∧
(a = n ∨ (∀ x, 0 ≤ a ∧ a ≤ x ∧ x < n → X[(x.toNat)]! > p)) :=
sorry
-- </vc-theorems>