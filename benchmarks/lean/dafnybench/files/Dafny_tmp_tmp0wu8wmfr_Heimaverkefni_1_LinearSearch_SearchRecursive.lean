-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def SearchRecursive (a : Array Int) (i : Int) (j : Int) (x : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem SearchRecursive_spec (a : Array Int) (i j x k : Int) :
(0 ≤ i ∧ i ≤ j ∧ j ≤ a.size) →
let k := SearchRecursive a i j x;
((i ≤ k ∧ k < j) ∨ k = -1) ∧
(k ≠ -1 → a[k.toNat]! = x) ∧
(k ≠ -1 → ∀ r, k < r ∧ r < j → a[r.toNat]! ≠ x) ∧
(k = -1 → ∀ r, i ≤ r ∧ r < j → a[r.toNat]! ≠ x) :=
sorry
-- </vc-theorems>