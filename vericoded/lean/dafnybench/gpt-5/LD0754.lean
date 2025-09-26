import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: no additional helpers needed.
-- </vc-helpers>

-- <vc-definitions>
def ArrayToSeq (a : Array Int) : Array Int :=
a
-- </vc-definitions>

-- <vc-theorems>
theorem ArrayToSeq_spec (a : Array Int) :
let s := ArrayToSeq a
s.size = a.size ∧
∀ i, 0 ≤ i ∧ i < a.size → s[i]! = a[i]! :=
by
  simpa [ArrayToSeq] using
    And.intro (rfl : a.size = a.size) (by intro i hi; rfl)
-- </vc-theorems>
