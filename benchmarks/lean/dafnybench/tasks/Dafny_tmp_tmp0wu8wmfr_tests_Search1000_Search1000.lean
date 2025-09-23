-- <vc-preamble>
partial def Is2Pow (n : Int) : Bool :=
if n < 1 then
false
else if n == 1 then
true
else
n % 2 == 0 ∧ Is2Pow (n/2)
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Search1000 (a : Array Int) (x : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem Search1000_spec (a : Array Int) (x : Int) (k : Int) :
a.size ≥ 1000 ∧
(∀ p q, 0 ≤ p ∧ p < q ∧ q < 1000 → a[p]! ≤ a[q]!) →
(0 ≤ k ∧ k ≤ 1000) ∧
(∀ r, 0 ≤ r ∧ r < k → a[r.toNat]! < x) ∧
(∀ r, k ≤ r ∧ r < 1000 → a[r.toNat]! ≥ x) :=
sorry
-- </vc-theorems>