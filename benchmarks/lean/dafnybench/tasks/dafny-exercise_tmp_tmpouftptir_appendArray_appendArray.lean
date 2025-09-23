-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def appendArray (a : Array Int) (b : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem appendArray_spec (a b c : Array Int) :
c = appendArray a b →
(c.size = a.size + b.size) ∧
(∀ i, 0 ≤ i ∧ i < a.size → a[i]! = c[i]!) ∧
(∀ i, 0 ≤ i ∧ i < b.size → b[i]! = c[a.size + i]!) :=
sorry
-- </vc-theorems>