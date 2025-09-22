-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def arraySum (a : Array Int) (b : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem arraySum_spec (a b : Array Int) :
a.size = b.size →
let c := arraySum a b
c.size = a.size ∧
(∀ i, 0 ≤ i ∧ i < a.size → a[i]! + b[i]! = c[i]!) :=
sorry
-- </vc-theorems>