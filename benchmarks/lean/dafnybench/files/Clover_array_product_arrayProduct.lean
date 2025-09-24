-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def arrayProduct (a : Array Int) (b : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem arrayProduct_spec (a b : Array Int) :
a.size = b.size →
let c := arrayProduct a b
c.size = a.size ∧
(∀ i, 0 ≤ i ∧ i < a.size → i < c.size → a[i]! * b[i]! = c[i]!) :=
sorry
-- </vc-theorems>