import Mathlib
-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- LLM HELPER
open Std
-- LLM HELPER: no additional helpers required

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
  dsimp [ArrayToSeq]
  constructor
  · rfl
  · intro i h
    rfl

-- </vc-theorems>
