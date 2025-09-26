import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
-- A trivial helper lemma for future use
theorem LLM_helper_trivial (x : Int) : x = x := rfl

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
