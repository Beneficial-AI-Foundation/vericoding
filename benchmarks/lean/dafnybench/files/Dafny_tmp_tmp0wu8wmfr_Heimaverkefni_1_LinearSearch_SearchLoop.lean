-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def SearchLoop (a : Array Int) (i j x : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem SearchLoop_spec (a : Array Int) (i j x : Int) :
(0 ≤ i ∧ i ≤ j ∧ j ≤ a.size) →
let k := SearchLoop a i j x
(i ≤ k ∧ k < j ∨ k = -1) ∧
(k ≠ -1 → a[k.toNat]! = x) ∧
(k ≠ -1 → ∀ r, k < r ∧ r < j → a[r.toNat]! ≠ x) ∧
(k = -1 → ∀ r, i ≤ r ∧ r < j → a[r.toNat]! ≠ x) :=
sorry
-- </vc-theorems>