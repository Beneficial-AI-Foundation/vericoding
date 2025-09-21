-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def intDiv (n : Int) (d : Int) : (Int × Int) :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem intDiv_spec (n d : Int) :
n ≥ d ∧ n ≥ 0 ∧ d > 0 →
let (q, r) := intDiv n d
(d*q + r = n) ∧ (0 ≤ q) ∧ (q ≤ n/2) ∧ (0 ≤ r) ∧ (r < d) :=
sorry
-- </vc-theorems>