import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- No helpers needed currently.
-- </vc-helpers>

-- <vc-definitions>
def MedianLength (a b : Int) : Int :=
(a + b) / 2
-- </vc-definitions>

-- <vc-theorems>
theorem MedianLength_spec (a b : Int) :
a > 0 ∧ b > 0 →
MedianLength a b = (a + b) / 2 :=
by
  intro _
  rfl
-- </vc-theorems>
