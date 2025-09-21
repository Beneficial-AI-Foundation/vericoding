-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Maximum (values : Array Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem Maximum_spec (values : Array Int) (max : Int) :
values.size > 0 →
(∃ i:Fin values.size, values[i]! = max) ∧
(∀ i, 0 ≤ i ∧ i < values.size → values[i]! ≤ max) :=
sorry
-- </vc-theorems>