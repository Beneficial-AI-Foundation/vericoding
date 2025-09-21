-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def mroot1 (n : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem mroot1_spec (n : Int) :
n ≥ 0 →
let r := mroot1 n
r ≥ 0 ∧ r * r ≤ n ∧ n < (r + 1) * (r + 1) :=
sorry
-- </vc-theorems>