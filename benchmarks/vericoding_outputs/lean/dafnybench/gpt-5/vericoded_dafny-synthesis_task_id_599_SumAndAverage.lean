import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- no helpers needed
-- </vc-helpers>

-- <vc-definitions>
def SumAndAverage (n : Int) : Int × Float :=
(n * (n + 1) / 2, Float.ofInt (n * (n + 1) / 2) / Float.ofInt n)
-- </vc-definitions>

-- <vc-theorems>
theorem SumAndAverage_spec (n : Int) :
n > 0 →
let (sum, average) := SumAndAverage n
sum = n * (n + 1) / 2 ∧
average = Float.ofInt sum / Float.ofInt n  :=
by
  intro _
  let s : Int := n * (n + 1) / 2
  simpa [SumAndAverage, s] using And.intro rfl rfl
-- </vc-theorems>
