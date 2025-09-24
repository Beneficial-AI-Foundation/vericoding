-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def SumOfCommonDivisors (a : Int) (b : Int) : Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem SumOfCommonDivisors_spec (a b : Int) :
a > 0 ∧ b > 0 →
let sum := SumOfCommonDivisors a b
sum ≥ 0 ∧
(∀ d, 1 ≤ d ∧ d ≤ a ∧ d ≤ b ∧ a % d = 0 ∧ b % d = 0 → sum ≥ d) :=
sorry
-- </vc-theorems>