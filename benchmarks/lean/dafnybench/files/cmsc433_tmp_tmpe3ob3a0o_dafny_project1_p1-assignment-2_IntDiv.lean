-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def IntDiv (m : Int) (n : Int) : Int × Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem IntDiv_spec (m n : Int) :
n > 0 →
let (d, r) := IntDiv m n
m = n * d + r ∧ 0 ≤ r ∧ r < n :=
sorry
-- </vc-theorems>