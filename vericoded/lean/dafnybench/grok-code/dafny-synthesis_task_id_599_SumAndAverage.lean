import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def SumAndAverage (n : Int) : Int × Float :=
let sum : Int := n * (n + 1) / 2
  let avg : Float := Float.ofInt sum / Float.ofInt n
  (sum, avg)
-- </vc-definitions>

-- <vc-theorems>
theorem SumAndAverage_spec (n : Int) :
n > 0 →
let (sum, average) := SumAndAverage n
sum = n * (n + 1) / 2 ∧
average = Float.ofInt sum / Float.ofInt n  :=
by
  intro h
  unfold SumAndAverage
  simp
-- </vc-theorems>
