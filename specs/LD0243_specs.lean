-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Search (s : Array Int) (x : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem Search_spec (s : Array Int) (x : Int) (k : Int) :
(∀ p q, 0 ≤ p → p < q → q < s.size → s[p]! ≤ s[q]!) →
(k = Search s x) →
(0 ≤ k ∧ k ≤ s.size) ∧
(∀ i, 0 ≤ i → i < k → s[i.toNat]! ≤ x) ∧
(∀ i, k ≤ i → i < s.size → s[i.toNat]! ≥ x) :=
sorry
-- </vc-theorems>