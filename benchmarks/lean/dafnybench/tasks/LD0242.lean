-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def SearchRecursive (a : Array Float) (i j : Int) (x : Float) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem SearchRecursive_spec
(a : Array Float) (i j : Int) (x : Float) :
(0 ≤ i ∧ i ≤ j ∧ j ≤ a.size) →
(∀ p q, i ≤ p ∧ p < q ∧ q < j → a[p.toNat]! ≥ a[q.toNat]!) →
let k := SearchRecursive a i j x
i ≤ k ∧ k ≤ j ∧
(∀ r, i ≤ r ∧ r < k → a[r.toNat]! ≥ x) ∧
(∀ r, k ≤ r ∧ r < j → a[r.toNat]! < x) :=
sorry
-- </vc-theorems>