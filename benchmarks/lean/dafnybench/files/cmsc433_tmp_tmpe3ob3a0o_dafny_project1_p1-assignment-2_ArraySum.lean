-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ArraySum (a b : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ArraySum_spec (a b : Array Int) :
a.size = b.size →
let c := ArraySum a b
c.size = a.size ∧
(∀ i, 0 ≤ i ∧ i < c.size → c[i]! = a[i]! + b[i]!) :=
sorry
-- </vc-theorems>