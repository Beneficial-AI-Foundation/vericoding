-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def SumAndAverage (n : Int) : Int × Float :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem SumAndAverage_spec (n : Int) :
n > 0 →
let (sum, average) := SumAndAverage n
sum = n * (n + 1) / 2 ∧
average = Float.ofInt sum / Float.ofInt n  :=
sorry
-- </vc-theorems>