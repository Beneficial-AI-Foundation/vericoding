-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def single (x : Array Int) (y : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem single_spec (x y : Array Int) :
x.size > 0 ∧ y.size > 0 →
∀ (result : Array Int), single x y = result →
result.size = x.size + y.size ∧
(∀ i:Fin x.size, i < x.size → result[i]! = x[i]!) ∧
(∀ i:Fin y.size, i < y.size → result[x.size + i]! = y[i]!) :=
sorry
-- </vc-theorems>