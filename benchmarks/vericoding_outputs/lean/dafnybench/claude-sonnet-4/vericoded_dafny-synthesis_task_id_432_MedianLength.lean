import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- Helper lemmas for MedianLength
-- </vc-helpers>

-- <vc-definitions>
def MedianLength (a b : Int) : Int :=
(a + b) / 2
-- </vc-definitions>

-- <vc-theorems>
theorem MedianLength_spec (a b : Int) :
a > 0 ∧ b > 0 →
MedianLength a b = (a + b) / 2 :=
fun _ => rfl
-- </vc-theorems>
