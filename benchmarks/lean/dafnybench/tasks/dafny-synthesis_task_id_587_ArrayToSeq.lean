-- <vc-preamble>
-- </vc-preamble>

-- <vc-helpers>
-- </vc-helpers>

-- <vc-definitions>
def ArrayToSeq (a : Array Int) : Array Int :=
sorry
-- </vc-definitions>

-- <vc-theorems>
theorem ArrayToSeq_spec (a : Array Int) :
let s := ArrayToSeq a
s.size = a.size ∧
∀ i, 0 ≤ i ∧ i < a.size → s[i]! = a[i]! :=
sorry
-- </vc-theorems>