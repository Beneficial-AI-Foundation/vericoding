-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def join (a : Array Int) (b : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem join_spec (a b : Array Int) :
let c := join a b
c.size = a.size + b.size ∧
(∀ i, 0 ≤ i ∧ i < a.size → c[i]! = a[i]!) ∧
(∀ i j, a.size ≤ i ∧ i < c.size ∧
0 ≤ j ∧ j < b.size ∧
i - j = a.size → c[i]! = b[j]!) :=
sorry
-- </vc-theorems>