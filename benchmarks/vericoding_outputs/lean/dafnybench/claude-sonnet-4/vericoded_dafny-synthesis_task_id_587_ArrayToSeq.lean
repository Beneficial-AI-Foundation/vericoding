import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER: No additional helpers needed for this simple case
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
⟨rfl, fun i _ => rfl⟩
-- </vc-theorems>
