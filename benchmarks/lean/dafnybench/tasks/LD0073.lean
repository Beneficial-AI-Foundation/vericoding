-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def Min_ (x y : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem Min_spec (x y z : Int) :
z = Min_ x y →
((x ≤ y → z = x) ∧
(x > y → z = y)) :=
sorry
-- </vc-theorems>