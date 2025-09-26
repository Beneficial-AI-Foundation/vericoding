import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>

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
  constructor
  · rfl
  · intro i ⟨hi_nonneg, hi_lt⟩
    rfl
-- </vc-theorems>
