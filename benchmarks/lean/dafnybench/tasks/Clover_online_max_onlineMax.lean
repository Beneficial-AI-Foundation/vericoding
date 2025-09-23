-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def onlineMax (a : Array Int) (x : Int) : Int × Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem onlineMax_spec (a : Array Int) (x : Int) (m p : Int) :
(1 ≤ x ∧ x < a.size) →
(a.size ≠ 0) →
let (m, p) := onlineMax a x;
(x ≤ p ∧ p < a.size) ∧
(∀ i, 0 ≤ i ∧ i < x → a[i.toNat]! ≤ m) ∧
(∃ i, 0 ≤ i ∧ i < x ∧ a[i.toNat]! = m) ∧
(x ≤ p ∧ p < a.size - 1 → (∀ i, 0 ≤ i ∧ i < p → a[i.toNat]! < a[p.toNat]!)) ∧
((∀ i, x ≤ i ∧ i < a.size ∧ a[i.toNat]! ≤ m) → p = a.size - 1) :=
sorry
-- </vc-theorems>