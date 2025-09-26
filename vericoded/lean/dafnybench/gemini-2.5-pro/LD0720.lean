import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>

-- </vc-helpers>

-- <vc-definitions>
def MedianLength (a b : Int) : Int :=
if a > 0 ∧ b > 0 then (a + b) / 2 else 0
-- </vc-definitions>

-- <vc-theorems>
theorem MedianLength_spec (a b : Int) :
a > 0 ∧ b > 0 →
MedianLength a b = (a + b) / 2 :=
by
  intro h
  simp [MedianLength, h]
-- </vc-theorems>
