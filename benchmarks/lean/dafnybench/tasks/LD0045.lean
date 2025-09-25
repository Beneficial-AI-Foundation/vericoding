-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def concat (a : Array Int) (b : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem concat_spec (a b : Array Int) :
let c := concat a b
c.size = b.size + a.size ∧
(∀ k, 0 ≤ k ∧ k < a.size → c[k]! = a[k]!) ∧
(∀ k, 0 ≤ k ∧ k < b.size → c[k + a.size]! = b[k]!) :=
sorry
-- </vc-theorems>