-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def LastDigit (n : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem LastDigit_spec (n : Int) :
n ≥ 0 →
let d := LastDigit n
0 ≤ d ∧ d < 10 ∧ n % 10 = d :=
sorry
-- </vc-theorems>