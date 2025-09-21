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
def Search2PowLoop (a : Array Int) (i : Int) (n : Int) (x : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem Search2PowLoop_spec
(a : Array Int) (i : Int) (n : Int) (x : Int) :
(0 ≤ i) →
(i + n ≤ a.size) →
(∀ p q, i ≤ p → p < q → q < i + n → a[p.toNat]! ≤ a[q.toNat]!) →
Is2Pow (n + 1) →
let k := Search2PowLoop a i n x
i ≤ k ∧ k ≤ i + n ∧
(∀ r, i ≤ r → r < k → a[r.toNat]! < x) ∧
(∀ r, k ≤ r → r < i + n → a[r.toNat]! ≥ x) :=
sorry
-- </vc-theorems>